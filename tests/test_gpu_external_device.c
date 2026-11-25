/* A context that runs on a Vulkan device someone else owns.
 *
 * The device is borrowed from an ordinary context, which is the easiest real
 * Vulkan device a test can get without writing a second device builder. What is
 * checked: the bad inputs are refused, an adopting context runs an operation and
 * gets the same answer as the owner, its queue submissions go through the lock
 * callbacks one at a time, and destroying it leaves the owner's device and
 * instance alone (the owner still works afterwards).
 *
 * Exit 77 (skipped) when there is no Vulkan device, and for the operation steps
 * when the build has no GPU SPIR-V.
 */
#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include "tinyvdb_gpu.h"
#include "tinyvdb_gpu_resident.h"

static int failures = 0;
#define CHECK(cond, msg) do { if (!(cond)) { printf("FAIL: %s\n", msg); ++failures; } } while (0)

typedef struct { int depth, max_depth, locks, unlocks; } lock_counter;

static void lock_cb(void* user) {
  lock_counter* c = (lock_counter*)user;
  ++c->locks;
  ++c->depth;
  if (c->depth > c->max_depth) c->max_depth = c->depth;
}

static void unlock_cb(void* user) {
  lock_counter* c = (lock_counter*)user;
  ++c->unlocks;
  --c->depth;
}

static int sphere(tvdb_gpu_context_t* ctx, tvdb_dense_grid* out) {
  const float center[3] = { 0.0f, 0.0f, 0.0f };
  tvdb_error_t e;
  memset(&e, 0, sizeof e);
  memset(out, 0, sizeof *out);
  return tvdb_gpu_level_set_sphere(ctx, 1.0f, center, 0.1f, 3.0f, out, &e) == TVDB_OK;
}

static int same_grid(const tvdb_dense_grid* a, const tvdb_dense_grid* b) {
  if (a->nx != b->nx || a->ny != b->ny || a->nz != b->nz) return 0;
  const size_t n = (size_t)a->nx * (size_t)a->ny * (size_t)a->nz;
  return n > 0 && memcmp(a->data, b->data, n * sizeof(float)) == 0;
}

static int resident_sum_uses_lock(tvdb_gpu_context_t* ctx, lock_counter* locks) {
  const tvdb_gpu_grid_desc_t desc = { 2, 2, 2, 1, TVDB_GPU_F32, 0, 0, 0, 1 };
  const float input_a[8] = { 1, 2, 3, 4, 5, 6, 7, 8 };
  const float input_b[8] = { 8, 7, 6, 5, 4, 3, 2, 1 };
  const float expected[8] = { 9, 9, 9, 9, 9, 9, 9, 9 };
  float result[8] = { 0 };
  tvdb_gpu_dense_grid_t *a = NULL, *b = NULL, *out = NULL;
  tvdb_error_t err = { 0 };
  int ok = 0;

  if (tvdb_gpu_dense_grid_create(ctx, &desc, &a, &err) != TVDB_OK ||
      tvdb_gpu_dense_grid_create(ctx, &desc, &b, &err) != TVDB_OK ||
      tvdb_gpu_dense_grid_create(ctx, &desc, &out, &err) != TVDB_OK ||
      tvdb_gpu_dense_grid_upload(a, input_a, sizeof input_a, &err) != TVDB_OK ||
      tvdb_gpu_dense_grid_upload(b, input_b, sizeof input_b, &err) != TVDB_OK) goto done;

  const int before = locks->locks;
  if (tvdb_gpu_comp_resident(ctx, a, b, 2, out, &err) != TVDB_OK) goto done;
  const int resident_locked = locks->locks > before;
  if (tvdb_gpu_dense_grid_download(out, result, sizeof result, &err) != TVDB_OK) goto done;
  ok = memcmp(result, expected, sizeof result) == 0 && resident_locked &&
       locks->locks == locks->unlocks && locks->depth == 0 && locks->max_depth == 1;

done:
  tvdb_gpu_dense_grid_destroy(out);
  tvdb_gpu_dense_grid_destroy(b);
  tvdb_gpu_dense_grid_destroy(a);
  return ok;
}

int main(void) {
  tvdb_error_t e;
  memset(&e, 0, sizeof e);
  tvdb_gpu_context_t* owner = NULL;
  if (tvdb_gpu_context_create(TVDB_GPU_BACKEND_VULKAN, 0, &owner, &e) != TVDB_OK) {
    printf("no vulkan context\n");
    return 77;
  }

  tvdb_gpu_vulkan_device_t dev;
  CHECK(tvdb_gpu_context_vulkan_device(owner, &dev, &e) == TVDB_OK, "owner gives its device");
  CHECK(tvdb_gpu_context_vulkan_device(NULL, &dev, &e) == TVDB_ERROR_INVALID_ARGUMENT, "NULL context has no device");

  /* Inputs that must be refused, and must leave *out NULL. */
  {
    tvdb_gpu_vulkan_device_t bad;
    tvdb_gpu_context_t* ctx = (tvdb_gpu_context_t*)1;
    CHECK(tvdb_gpu_context_create_vulkan_external(NULL, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "NULL device description refused");
    CHECK(tvdb_gpu_context_create_vulkan_external(&dev, NULL, &e) == TVDB_ERROR_INVALID_ARGUMENT,
          "NULL output refused");

    bad = dev; bad.get_instance_proc_addr = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "missing vkGetInstanceProcAddr refused");
    bad = dev; bad.instance = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "missing instance refused");
    bad = dev; bad.physical_device = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "missing physical device refused");
    bad = dev; bad.device = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "missing device refused");
    bad = dev; bad.queue = NULL;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "missing queue refused");

    lock_counter unused;
    memset(&unused, 0, sizeof unused);
    bad = dev; bad.lock_queue = lock_cb; bad.unlock_queue = NULL; bad.user = &unused;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "a lock without an unlock refused");
    bad = dev; bad.queue_family = UINT32_MAX;
    CHECK(tvdb_gpu_context_create_vulkan_external(&bad, &ctx, &e) == TVDB_ERROR_INVALID_ARGUMENT && ctx == NULL,
          "out of range queue family refused");
  }

  lock_counter locks;
  memset(&locks, 0, sizeof locks);
  tvdb_gpu_vulkan_device_t shared = dev;
  shared.lock_queue = lock_cb;
  shared.unlock_queue = unlock_cb;
  shared.user = &locks;

  tvdb_gpu_context_t* guest = NULL;
  CHECK(tvdb_gpu_context_create_vulkan_external(&shared, &guest, &e) == TVDB_OK && guest != NULL,
        "an adopting context is created");
  if (!guest) {
    tvdb_gpu_context_destroy(owner);
    return 1;
  }

  tvdb_gpu_context_info_t info;
  memset(&info, 0, sizeof info);
  CHECK(tvdb_gpu_context_info(guest, &info, &e) == TVDB_OK && info.backend == TVDB_GPU_BACKEND_VULKAN,
        "the adopting context reports Vulkan");

  int ran = 0;
  if (tvdb_gpu_spirv_available()) {
    tvdb_dense_grid from_owner, from_guest, after;
    memset(&from_owner, 0, sizeof from_owner);
    memset(&from_guest, 0, sizeof from_guest);
    memset(&after, 0, sizeof after);

    CHECK(sphere(owner, &from_owner), "owner runs the sphere");
    CHECK(sphere(guest, &from_guest), "adopting context runs the sphere");
    CHECK(from_owner.data && from_guest.data && same_grid(&from_owner, &from_guest),
          "both contexts give the same grid");
    CHECK(locks.locks > 0, "submissions went through the lock");
    CHECK(locks.locks == locks.unlocks, "every lock was unlocked");
    CHECK(locks.depth == 0 && locks.max_depth == 1, "locks were never nested");
    CHECK(resident_sum_uses_lock(guest, &locks), "resident submission uses the shared-queue lock");

    tvdb_gpu_context_destroy(guest);
    guest = NULL;

    /* The owner's device and instance must have survived the guest. */
    CHECK(sphere(owner, &after), "owner still runs after the guest is destroyed");
    CHECK(after.data && same_grid(&from_owner, &after), "owner still gives the same grid");

    tvdb_dense_grid_free(&from_owner);
    tvdb_dense_grid_free(&from_guest);
    tvdb_dense_grid_free(&after);
    ran = 1;
  } else {
    tvdb_gpu_context_destroy(guest);
    guest = NULL;
    printf("operation steps skipped: built without GPU SPIR-V\n");
  }

  tvdb_gpu_context_destroy(owner);
  if (failures) return 1;
  return ran ? 0 : 77;
}
