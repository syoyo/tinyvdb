#if TVDBVIEW_HAS_VULKAN_HEADERS
struct VkLoaded {
  void* lib = nullptr;
  PFN_vkGetInstanceProcAddr GetInstanceProcAddr = nullptr;
  PFN_vkCreateInstance CreateInstance = nullptr;
  PFN_vkDestroyInstance DestroyInstance = nullptr;
  PFN_vkEnumeratePhysicalDevices EnumeratePhysicalDevices = nullptr;
  PFN_vkGetPhysicalDeviceQueueFamilyProperties GetPhysicalDeviceQueueFamilyProperties = nullptr;
  PFN_vkGetPhysicalDeviceMemoryProperties GetPhysicalDeviceMemoryProperties = nullptr;
  PFN_vkCreateDevice CreateDevice = nullptr;
  PFN_vkGetDeviceProcAddr GetDeviceProcAddr = nullptr;
  PFN_vkDestroyDevice DestroyDevice = nullptr;
  PFN_vkGetDeviceQueue GetDeviceQueue = nullptr;
  PFN_vkCreateBuffer CreateBuffer = nullptr;
  PFN_vkDestroyBuffer DestroyBuffer = nullptr;
  PFN_vkGetBufferMemoryRequirements GetBufferMemoryRequirements = nullptr;
  PFN_vkAllocateMemory AllocateMemory = nullptr;
  PFN_vkFreeMemory FreeMemory = nullptr;
  PFN_vkBindBufferMemory BindBufferMemory = nullptr;
  PFN_vkMapMemory MapMemory = nullptr;
  PFN_vkUnmapMemory UnmapMemory = nullptr;
  PFN_vkCreateDescriptorSetLayout CreateDescriptorSetLayout = nullptr;
  PFN_vkDestroyDescriptorSetLayout DestroyDescriptorSetLayout = nullptr;
  PFN_vkCreateDescriptorPool CreateDescriptorPool = nullptr;
  PFN_vkDestroyDescriptorPool DestroyDescriptorPool = nullptr;
  PFN_vkAllocateDescriptorSets AllocateDescriptorSets = nullptr;
  PFN_vkUpdateDescriptorSets UpdateDescriptorSets = nullptr;
  PFN_vkCreateShaderModule CreateShaderModule = nullptr;
  PFN_vkDestroyShaderModule DestroyShaderModule = nullptr;
  PFN_vkCreatePipelineLayout CreatePipelineLayout = nullptr;
  PFN_vkDestroyPipelineLayout DestroyPipelineLayout = nullptr;
  PFN_vkCreateComputePipelines CreateComputePipelines = nullptr;
  PFN_vkDestroyPipeline DestroyPipeline = nullptr;
  PFN_vkCreateCommandPool CreateCommandPool = nullptr;
  PFN_vkDestroyCommandPool DestroyCommandPool = nullptr;
  PFN_vkAllocateCommandBuffers AllocateCommandBuffers = nullptr;
  PFN_vkBeginCommandBuffer BeginCommandBuffer = nullptr;
  PFN_vkEndCommandBuffer EndCommandBuffer = nullptr;
  PFN_vkResetCommandBuffer ResetCommandBuffer = nullptr;
  PFN_vkCmdBindPipeline CmdBindPipeline = nullptr;
  PFN_vkCmdBindDescriptorSets CmdBindDescriptorSets = nullptr;
  PFN_vkCmdDispatch CmdDispatch = nullptr;
  PFN_vkCreateFence CreateFence = nullptr;
  PFN_vkDestroyFence DestroyFence = nullptr;
  PFN_vkResetFences ResetFences = nullptr;
  PFN_vkWaitForFences WaitForFences = nullptr;
  PFN_vkQueueSubmit QueueSubmit = nullptr;
  PFN_vkDeviceWaitIdle DeviceWaitIdle = nullptr;
};

struct VkHostBuffer {
  VkBuffer buffer = VK_NULL_HANDLE;
  VkDeviceMemory memory = VK_NULL_HANDLE;
  VkDeviceSize size = 0;
  void* mapped = nullptr;
};

struct alignas(16) VkVec4 {
  float x, y, z, w;
};

struct alignas(16) VkIVec4 {
  int32_t x, y, z, w;
};

struct VkPathTraceParams {
  VkVec4 camera_pos;
  VkVec4 camera_forward;
  VkVec4 camera_right;
  VkVec4 camera_up;
  VkVec4 volume_min;
  VkVec4 volume_max;
  VkVec4 clip_min;
  VkVec4 clip_max;
  VkVec4 settings0;
  VkVec4 settings1;
  VkVec4 settings2;
  VkIVec4 settings_i0;
  VkIVec4 settings_i1;
  VkIVec4 settings_i2;
  VkVec4 settings3;
};

struct VulkanPathTraceBackend {
  VkLoaded vk;
  VkInstance instance = VK_NULL_HANDLE;
  VkPhysicalDevice physical_device = VK_NULL_HANDLE;
  VkDevice device = VK_NULL_HANDLE;
  VkQueue queue = VK_NULL_HANDLE;
  uint32_t queue_family = 0;
  VkPhysicalDeviceMemoryProperties memory_props = {};
  VkDescriptorSetLayout descriptor_layout = VK_NULL_HANDLE;
  VkDescriptorPool descriptor_pool = VK_NULL_HANDLE;
  VkDescriptorSet descriptor_set = VK_NULL_HANDLE;
  VkPipelineLayout pipeline_layout = VK_NULL_HANDLE;
  VkPipeline pipeline = VK_NULL_HANDLE;
  VkShaderModule shader = VK_NULL_HANDLE;
  VkCommandPool command_pool = VK_NULL_HANDLE;
  VkCommandBuffer command_buffer = VK_NULL_HANDLE;
  VkFence fence = VK_NULL_HANDLE;
  VkHostBuffer density;
  VkHostBuffer accum;
  VkHostBuffer rgba;
  VkHostBuffer params;
  std::string buffer_key;
  std::string error;
};

void* LoadSharedLibrary(const char* name) {
#if defined(__unix__) || defined(__APPLE__)
  return dlopen(name, RTLD_NOW | RTLD_LOCAL);
#else
  (void)name;
  return nullptr;
#endif
}

void* LoadSymbol(void* lib, const char* name) {
#if defined(__unix__) || defined(__APPLE__)
  return dlsym(lib, name);
#else
  (void)lib;
  (void)name;
  return nullptr;
#endif
}

void CloseSharedLibrary(void* lib) {
#if defined(__unix__) || defined(__APPLE__)
  if (lib) dlclose(lib);
#else
  (void)lib;
#endif
}

bool VkOk(VkResult result, const char* label, VulkanPathTraceBackend* backend) {
  if (result == VK_SUCCESS) return true;
  backend->error = std::string(label) + " failed: " + std::to_string(static_cast<int>(result));
  return false;
}

bool LoadVulkanLibrary(VulkanPathTraceBackend* backend) {
  backend->vk.lib = LoadSharedLibrary("libvulkan.so.1");
  if (!backend->vk.lib) backend->vk.lib = LoadSharedLibrary("libvulkan.so");
  if (!backend->vk.lib) {
    backend->error = "libvulkan.so not found";
    return false;
  }
  backend->vk.GetInstanceProcAddr =
      reinterpret_cast<PFN_vkGetInstanceProcAddr>(LoadSymbol(backend->vk.lib, "vkGetInstanceProcAddr"));
  backend->vk.CreateInstance =
      reinterpret_cast<PFN_vkCreateInstance>(LoadSymbol(backend->vk.lib, "vkCreateInstance"));
  if (!backend->vk.GetInstanceProcAddr || !backend->vk.CreateInstance) {
    backend->error = "Vulkan loader entry points not found";
    return false;
  }
  return true;
}

template <typename T>
bool LoadVkInstanceFunc(VulkanPathTraceBackend* backend, T* fn, const char* name) {
  *fn = reinterpret_cast<T>(backend->vk.GetInstanceProcAddr(backend->instance, name));
  if (*fn) return true;
  backend->error = std::string("missing Vulkan instance function: ") + name;
  return false;
}

template <typename T>
bool LoadVkDeviceFunc(VulkanPathTraceBackend* backend, T* fn, const char* name) {
  *fn = reinterpret_cast<T>(backend->vk.GetDeviceProcAddr(backend->device, name));
  if (*fn) return true;
  backend->error = std::string("missing Vulkan device function: ") + name;
  return false;
}

uint32_t FindMemoryType(const VulkanPathTraceBackend& backend, uint32_t bits,
                        VkMemoryPropertyFlags props) {
  for (uint32_t i = 0; i < backend.memory_props.memoryTypeCount; ++i) {
    if ((bits & (1u << i)) &&
        (backend.memory_props.memoryTypes[i].propertyFlags & props) == props) {
      return i;
    }
  }
  return UINT32_MAX;
}

bool CreateHostBuffer(VulkanPathTraceBackend* backend, VkDeviceSize size,
                      VkBufferUsageFlags usage, VkHostBuffer* out) {
  VkBufferCreateInfo bci = {};
  bci.sType = VK_STRUCTURE_TYPE_BUFFER_CREATE_INFO;
  bci.size = size;
  bci.usage = usage;
  bci.sharingMode = VK_SHARING_MODE_EXCLUSIVE;
  if (!VkOk(backend->vk.CreateBuffer(backend->device, &bci, nullptr, &out->buffer),
            "vkCreateBuffer", backend)) {
    return false;
  }
  VkMemoryRequirements req = {};
  backend->vk.GetBufferMemoryRequirements(backend->device, out->buffer, &req);
  const uint32_t memory_type =
      FindMemoryType(*backend, req.memoryTypeBits,
                     VK_MEMORY_PROPERTY_HOST_VISIBLE_BIT | VK_MEMORY_PROPERTY_HOST_COHERENT_BIT);
  if (memory_type == UINT32_MAX) {
    backend->error = "no host-visible coherent Vulkan memory type";
    return false;
  }
  VkMemoryAllocateInfo mai = {};
  mai.sType = VK_STRUCTURE_TYPE_MEMORY_ALLOCATE_INFO;
  mai.allocationSize = req.size;
  mai.memoryTypeIndex = memory_type;
  if (!VkOk(backend->vk.AllocateMemory(backend->device, &mai, nullptr, &out->memory),
            "vkAllocateMemory", backend)) {
    return false;
  }
  if (!VkOk(backend->vk.BindBufferMemory(backend->device, out->buffer, out->memory, 0),
            "vkBindBufferMemory", backend)) {
    return false;
  }
  if (!VkOk(backend->vk.MapMemory(backend->device, out->memory, 0, size, 0, &out->mapped),
            "vkMapMemory", backend)) {
    return false;
  }
  out->size = size;
  return true;
}

void DestroyHostBuffer(VulkanPathTraceBackend* backend, VkHostBuffer* buf) {
  if (!backend || !backend->device) return;
  if (buf->mapped && backend->vk.UnmapMemory) backend->vk.UnmapMemory(backend->device, buf->memory);
  if (buf->buffer && backend->vk.DestroyBuffer) backend->vk.DestroyBuffer(backend->device, buf->buffer, nullptr);
  if (buf->memory && backend->vk.FreeMemory) backend->vk.FreeMemory(backend->device, buf->memory, nullptr);
  *buf = VkHostBuffer{};
}

void DestroyVulkanPathTrace(AppState* app) {
  VulkanPathTraceBackend* backend = app ? app->vulkan_path_trace : nullptr;
  if (!backend) return;
  if (backend->device && backend->vk.DeviceWaitIdle) backend->vk.DeviceWaitIdle(backend->device);
  DestroyHostBuffer(backend, &backend->density);
  DestroyHostBuffer(backend, &backend->accum);
  DestroyHostBuffer(backend, &backend->rgba);
  DestroyHostBuffer(backend, &backend->params);
  if (backend->device) {
    if (backend->fence && backend->vk.DestroyFence) backend->vk.DestroyFence(backend->device, backend->fence, nullptr);
    if (backend->command_pool && backend->vk.DestroyCommandPool) backend->vk.DestroyCommandPool(backend->device, backend->command_pool, nullptr);
    if (backend->pipeline && backend->vk.DestroyPipeline) backend->vk.DestroyPipeline(backend->device, backend->pipeline, nullptr);
    if (backend->pipeline_layout && backend->vk.DestroyPipelineLayout) backend->vk.DestroyPipelineLayout(backend->device, backend->pipeline_layout, nullptr);
    if (backend->shader && backend->vk.DestroyShaderModule) backend->vk.DestroyShaderModule(backend->device, backend->shader, nullptr);
    if (backend->descriptor_pool && backend->vk.DestroyDescriptorPool) backend->vk.DestroyDescriptorPool(backend->device, backend->descriptor_pool, nullptr);
    if (backend->descriptor_layout && backend->vk.DestroyDescriptorSetLayout) backend->vk.DestroyDescriptorSetLayout(backend->device, backend->descriptor_layout, nullptr);
    if (backend->vk.DestroyDevice) backend->vk.DestroyDevice(backend->device, nullptr);
  }
  if (backend->instance && backend->vk.DestroyInstance) backend->vk.DestroyInstance(backend->instance, nullptr);
  CloseSharedLibrary(backend->vk.lib);
  delete backend;
  app->vulkan_path_trace = nullptr;
  app->path_trace_vulkan_available = false;
}

bool InitVulkanPathTrace(AppState* app) {
  if (app->vulkan_path_trace) return app->path_trace_vulkan_available;
  app->vulkan_path_trace = new VulkanPathTraceBackend();
  VulkanPathTraceBackend* backend = app->vulkan_path_trace;
  if (!LoadVulkanLibrary(backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkApplicationInfo ai = {};
  ai.sType = VK_STRUCTURE_TYPE_APPLICATION_INFO;
  ai.pApplicationName = "tvdbview";
  ai.apiVersion = VK_API_VERSION_1_1;
  VkInstanceCreateInfo ici = {};
  ici.sType = VK_STRUCTURE_TYPE_INSTANCE_CREATE_INFO;
  ici.pApplicationInfo = &ai;
  if (!VkOk(backend->vk.CreateInstance(&ici, nullptr, &backend->instance),
            "vkCreateInstance", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  if (!LoadVkInstanceFunc(backend, &backend->vk.DestroyInstance, "vkDestroyInstance") ||
      !LoadVkInstanceFunc(backend, &backend->vk.EnumeratePhysicalDevices, "vkEnumeratePhysicalDevices") ||
      !LoadVkInstanceFunc(backend, &backend->vk.GetPhysicalDeviceQueueFamilyProperties, "vkGetPhysicalDeviceQueueFamilyProperties") ||
      !LoadVkInstanceFunc(backend, &backend->vk.GetPhysicalDeviceMemoryProperties, "vkGetPhysicalDeviceMemoryProperties") ||
      !LoadVkInstanceFunc(backend, &backend->vk.CreateDevice, "vkCreateDevice") ||
      !LoadVkInstanceFunc(backend, &backend->vk.GetDeviceProcAddr, "vkGetDeviceProcAddr")) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  uint32_t physical_count = 0;
  if (!VkOk(backend->vk.EnumeratePhysicalDevices(backend->instance, &physical_count, nullptr),
            "vkEnumeratePhysicalDevices", backend) || physical_count == 0) {
    std::cout << "Vulkan backend unavailable: no physical devices\n";
    return false;
  }
  std::vector<VkPhysicalDevice> physical_devices(physical_count);
  backend->vk.EnumeratePhysicalDevices(backend->instance, &physical_count, physical_devices.data());
  for (VkPhysicalDevice pd : physical_devices) {
    uint32_t qcount = 0;
    backend->vk.GetPhysicalDeviceQueueFamilyProperties(pd, &qcount, nullptr);
    std::vector<VkQueueFamilyProperties> qprops(qcount);
    backend->vk.GetPhysicalDeviceQueueFamilyProperties(pd, &qcount, qprops.data());
    for (uint32_t i = 0; i < qcount; ++i) {
      if (qprops[i].queueFlags & VK_QUEUE_COMPUTE_BIT) {
        backend->physical_device = pd;
        backend->queue_family = i;
        break;
      }
    }
    if (backend->physical_device) break;
  }
  if (!backend->physical_device) {
    std::cout << "Vulkan backend unavailable: no compute queue\n";
    return false;
  }
  backend->vk.GetPhysicalDeviceMemoryProperties(backend->physical_device, &backend->memory_props);
  const float queue_priority = 1.0f;
  VkDeviceQueueCreateInfo qci = {};
  qci.sType = VK_STRUCTURE_TYPE_DEVICE_QUEUE_CREATE_INFO;
  qci.queueFamilyIndex = backend->queue_family;
  qci.queueCount = 1;
  qci.pQueuePriorities = &queue_priority;
  VkDeviceCreateInfo dci = {};
  dci.sType = VK_STRUCTURE_TYPE_DEVICE_CREATE_INFO;
  dci.queueCreateInfoCount = 1;
  dci.pQueueCreateInfos = &qci;
  if (!VkOk(backend->vk.CreateDevice(backend->physical_device, &dci, nullptr, &backend->device),
            "vkCreateDevice", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  if (!LoadVkDeviceFunc(backend, &backend->vk.DestroyDevice, "vkDestroyDevice") ||
      !LoadVkDeviceFunc(backend, &backend->vk.GetDeviceQueue, "vkGetDeviceQueue") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateBuffer, "vkCreateBuffer") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyBuffer, "vkDestroyBuffer") ||
      !LoadVkDeviceFunc(backend, &backend->vk.GetBufferMemoryRequirements, "vkGetBufferMemoryRequirements") ||
      !LoadVkDeviceFunc(backend, &backend->vk.AllocateMemory, "vkAllocateMemory") ||
      !LoadVkDeviceFunc(backend, &backend->vk.FreeMemory, "vkFreeMemory") ||
      !LoadVkDeviceFunc(backend, &backend->vk.BindBufferMemory, "vkBindBufferMemory") ||
      !LoadVkDeviceFunc(backend, &backend->vk.MapMemory, "vkMapMemory") ||
      !LoadVkDeviceFunc(backend, &backend->vk.UnmapMemory, "vkUnmapMemory") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateDescriptorSetLayout, "vkCreateDescriptorSetLayout") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyDescriptorSetLayout, "vkDestroyDescriptorSetLayout") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateDescriptorPool, "vkCreateDescriptorPool") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyDescriptorPool, "vkDestroyDescriptorPool") ||
      !LoadVkDeviceFunc(backend, &backend->vk.AllocateDescriptorSets, "vkAllocateDescriptorSets") ||
      !LoadVkDeviceFunc(backend, &backend->vk.UpdateDescriptorSets, "vkUpdateDescriptorSets") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateShaderModule, "vkCreateShaderModule") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyShaderModule, "vkDestroyShaderModule") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreatePipelineLayout, "vkCreatePipelineLayout") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyPipelineLayout, "vkDestroyPipelineLayout") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateComputePipelines, "vkCreateComputePipelines") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyPipeline, "vkDestroyPipeline") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateCommandPool, "vkCreateCommandPool") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyCommandPool, "vkDestroyCommandPool") ||
      !LoadVkDeviceFunc(backend, &backend->vk.AllocateCommandBuffers, "vkAllocateCommandBuffers") ||
      !LoadVkDeviceFunc(backend, &backend->vk.BeginCommandBuffer, "vkBeginCommandBuffer") ||
      !LoadVkDeviceFunc(backend, &backend->vk.EndCommandBuffer, "vkEndCommandBuffer") ||
      !LoadVkDeviceFunc(backend, &backend->vk.ResetCommandBuffer, "vkResetCommandBuffer") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CmdBindPipeline, "vkCmdBindPipeline") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CmdBindDescriptorSets, "vkCmdBindDescriptorSets") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CmdDispatch, "vkCmdDispatch") ||
      !LoadVkDeviceFunc(backend, &backend->vk.CreateFence, "vkCreateFence") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DestroyFence, "vkDestroyFence") ||
      !LoadVkDeviceFunc(backend, &backend->vk.ResetFences, "vkResetFences") ||
      !LoadVkDeviceFunc(backend, &backend->vk.WaitForFences, "vkWaitForFences") ||
      !LoadVkDeviceFunc(backend, &backend->vk.QueueSubmit, "vkQueueSubmit") ||
      !LoadVkDeviceFunc(backend, &backend->vk.DeviceWaitIdle, "vkDeviceWaitIdle")) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  backend->vk.GetDeviceQueue(backend->device, backend->queue_family, 0, &backend->queue);

  VkDescriptorSetLayoutBinding bindings[4] = {};
  for (uint32_t i = 0; i < 4; ++i) {
    bindings[i].binding = i;
    bindings[i].descriptorCount = 1;
    bindings[i].stageFlags = VK_SHADER_STAGE_COMPUTE_BIT;
    bindings[i].descriptorType = i == 3 ? VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER
                                         : VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  }
  VkDescriptorSetLayoutCreateInfo dlci = {};
  dlci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_LAYOUT_CREATE_INFO;
  dlci.bindingCount = 4;
  dlci.pBindings = bindings;
  if (!VkOk(backend->vk.CreateDescriptorSetLayout(backend->device, &dlci, nullptr,
                                                  &backend->descriptor_layout),
            "vkCreateDescriptorSetLayout", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkDescriptorPoolSize pool_sizes[2] = {};
  pool_sizes[0].type = VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
  pool_sizes[0].descriptorCount = 3;
  pool_sizes[1].type = VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER;
  pool_sizes[1].descriptorCount = 1;
  VkDescriptorPoolCreateInfo dpci = {};
  dpci.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_POOL_CREATE_INFO;
  dpci.maxSets = 1;
  dpci.poolSizeCount = 2;
  dpci.pPoolSizes = pool_sizes;
  if (!VkOk(backend->vk.CreateDescriptorPool(backend->device, &dpci, nullptr,
                                             &backend->descriptor_pool),
            "vkCreateDescriptorPool", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkDescriptorSetAllocateInfo dsai = {};
  dsai.sType = VK_STRUCTURE_TYPE_DESCRIPTOR_SET_ALLOCATE_INFO;
  dsai.descriptorPool = backend->descriptor_pool;
  dsai.descriptorSetCount = 1;
  dsai.pSetLayouts = &backend->descriptor_layout;
  if (!VkOk(backend->vk.AllocateDescriptorSets(backend->device, &dsai, &backend->descriptor_set),
            "vkAllocateDescriptorSets", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkShaderModuleCreateInfo smci = {};
  smci.sType = VK_STRUCTURE_TYPE_SHADER_MODULE_CREATE_INFO;
  smci.codeSize = kVulkanPathTraceSpv_len;
  smci.pCode = reinterpret_cast<const uint32_t*>(kVulkanPathTraceSpv);
  if (!VkOk(backend->vk.CreateShaderModule(backend->device, &smci, nullptr, &backend->shader),
            "vkCreateShaderModule", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkPipelineLayoutCreateInfo plci = {};
  plci.sType = VK_STRUCTURE_TYPE_PIPELINE_LAYOUT_CREATE_INFO;
  plci.setLayoutCount = 1;
  plci.pSetLayouts = &backend->descriptor_layout;
  if (!VkOk(backend->vk.CreatePipelineLayout(backend->device, &plci, nullptr,
                                             &backend->pipeline_layout),
            "vkCreatePipelineLayout", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkComputePipelineCreateInfo cpci = {};
  cpci.sType = VK_STRUCTURE_TYPE_COMPUTE_PIPELINE_CREATE_INFO;
  cpci.stage.sType = VK_STRUCTURE_TYPE_PIPELINE_SHADER_STAGE_CREATE_INFO;
  cpci.stage.stage = VK_SHADER_STAGE_COMPUTE_BIT;
  cpci.stage.module = backend->shader;
  cpci.stage.pName = "main";
  cpci.layout = backend->pipeline_layout;
  if (!VkOk(backend->vk.CreateComputePipelines(backend->device, VK_NULL_HANDLE, 1,
                                               &cpci, nullptr, &backend->pipeline),
            "vkCreateComputePipelines", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkCommandPoolCreateInfo cpool = {};
  cpool.sType = VK_STRUCTURE_TYPE_COMMAND_POOL_CREATE_INFO;
  cpool.flags = VK_COMMAND_POOL_CREATE_RESET_COMMAND_BUFFER_BIT;
  cpool.queueFamilyIndex = backend->queue_family;
  if (!VkOk(backend->vk.CreateCommandPool(backend->device, &cpool, nullptr,
                                          &backend->command_pool),
            "vkCreateCommandPool", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkCommandBufferAllocateInfo cbai = {};
  cbai.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_ALLOCATE_INFO;
  cbai.commandPool = backend->command_pool;
  cbai.level = VK_COMMAND_BUFFER_LEVEL_PRIMARY;
  cbai.commandBufferCount = 1;
  if (!VkOk(backend->vk.AllocateCommandBuffers(backend->device, &cbai, &backend->command_buffer),
            "vkAllocateCommandBuffers", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  VkFenceCreateInfo fci = {};
  fci.sType = VK_STRUCTURE_TYPE_FENCE_CREATE_INFO;
  if (!VkOk(backend->vk.CreateFence(backend->device, &fci, nullptr, &backend->fence),
            "vkCreateFence", backend)) {
    std::cout << "Vulkan backend unavailable: " << backend->error << "\n";
    return false;
  }
  app->path_trace_vulkan_available = true;
  std::cout << "Vulkan path trace backend available (runtime loaded).\n";
  return true;
}

bool EnsureVulkanPathTraceBuffers(AppState* app, const VolumeData& volume) {
  if (!InitVulkanPathTrace(app) || !app->path_trace_vulkan_available) return false;
  EnsurePathTraceBuffers(app);
  VulkanPathTraceBackend* backend = app->vulkan_path_trace;
  const std::string key = std::to_string(app->active_volume) + ":" +
                          std::to_string(app->path_trace_width) + "x" +
                          std::to_string(app->path_trace_height) + ":" +
                          std::to_string(volume.density.size());
  if (backend->buffer_key == key && backend->density.buffer) return true;
  backend->vk.DeviceWaitIdle(backend->device);
  DestroyHostBuffer(backend, &backend->density);
  DestroyHostBuffer(backend, &backend->accum);
  DestroyHostBuffer(backend, &backend->rgba);
  DestroyHostBuffer(backend, &backend->params);
  const VkDeviceSize density_size =
      static_cast<VkDeviceSize>(volume.density.size() * sizeof(float));
  const VkDeviceSize pixel_count =
      static_cast<VkDeviceSize>(app->path_trace_width) * app->path_trace_height;
  if (!CreateHostBuffer(backend, density_size, VK_BUFFER_USAGE_STORAGE_BUFFER_BIT,
                        &backend->density) ||
      !CreateHostBuffer(backend, pixel_count * sizeof(float) * 4,
                        VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &backend->accum) ||
      !CreateHostBuffer(backend, pixel_count * sizeof(uint32_t),
                        VK_BUFFER_USAGE_STORAGE_BUFFER_BIT, &backend->rgba) ||
      !CreateHostBuffer(backend, sizeof(VkPathTraceParams), VK_BUFFER_USAGE_UNIFORM_BUFFER_BIT,
                        &backend->params)) {
    std::cout << "Vulkan backend buffer setup failed: " << backend->error << "\n";
    return false;
  }
  std::memcpy(backend->density.mapped, volume.density.data(), static_cast<std::size_t>(density_size));
  std::memset(backend->accum.mapped, 0, static_cast<std::size_t>(backend->accum.size));
  std::memset(backend->rgba.mapped, 0, static_cast<std::size_t>(backend->rgba.size));
  VkDescriptorBufferInfo infos[4] = {};
  infos[0] = VkDescriptorBufferInfo{backend->density.buffer, 0, backend->density.size};
  infos[1] = VkDescriptorBufferInfo{backend->accum.buffer, 0, backend->accum.size};
  infos[2] = VkDescriptorBufferInfo{backend->rgba.buffer, 0, backend->rgba.size};
  infos[3] = VkDescriptorBufferInfo{backend->params.buffer, 0, backend->params.size};
  VkWriteDescriptorSet writes[4] = {};
  for (uint32_t i = 0; i < 4; ++i) {
    writes[i].sType = VK_STRUCTURE_TYPE_WRITE_DESCRIPTOR_SET;
    writes[i].dstSet = backend->descriptor_set;
    writes[i].dstBinding = i;
    writes[i].descriptorCount = 1;
    writes[i].descriptorType = i == 3 ? VK_DESCRIPTOR_TYPE_UNIFORM_BUFFER
                                      : VK_DESCRIPTOR_TYPE_STORAGE_BUFFER;
    writes[i].pBufferInfo = &infos[i];
  }
  backend->vk.UpdateDescriptorSets(backend->device, 4, writes, 0, nullptr);
  backend->buffer_key = key;
  ResetPathTrace(app);
  return true;
}

bool UpdatePathTraceVulkan(AppState* app) {
  if (app->active_volume >= app->scene.volumes.size()) return false;
  const VolumeData& volume = app->scene.volumes[app->active_volume];
  const Bounds bounds = ActiveVolumeBounds(*app);
  if (volume.density.empty() || !bounds.valid) return false;
  if (!EnsureVulkanPathTraceBuffers(app, volume)) return false;
  VulkanPathTraceBackend* backend = app->vulkan_path_trace;
  if (app->path_trace_completed_passes == 0) {
    if (backend->accum.mapped) std::memset(backend->accum.mapped, 0, static_cast<std::size_t>(backend->accum.size));
    if (backend->rgba.mapped) std::memset(backend->rgba.mapped, 0, static_cast<std::size_t>(backend->rgba.size));
  }
  Vec3 right;
  Vec3 up;
  app->camera.localAxes(&right, &up);
  const Vec3 eye = app->camera.eye();
  const Vec3 forward = Normalize(app->camera.target - eye);
  float value_offset = volume.min_value;
  float value_scale = (volume.max_value - volume.min_value) > 1.0e-8f
                          ? 1.0f / (volume.max_value - volume.min_value)
                          : 1.0f;
  if (app->manual_window) {
    value_offset = app->window_min;
    value_scale = (app->window_max - app->window_min) > 1.0e-8f
                      ? 1.0f / (app->window_max - app->window_min)
                      : 1.0f;
  }
  VkPathTraceParams params = {};
  params.camera_pos = {eye.x, eye.y, eye.z, 0.0f};
  params.camera_forward = {forward.x, forward.y, forward.z, 0.0f};
  params.camera_right = {right.x, right.y, right.z, 0.0f};
  params.camera_up = {up.x, up.y, up.z, 0.0f};
  params.volume_min = {bounds.min.x, bounds.min.y, bounds.min.z, 0.0f};
  params.volume_max = {bounds.max.x, bounds.max.y, bounds.max.z, 0.0f};
  params.clip_min = {app->clip_enabled ? app->clip_min[0] : 0.0f,
                     app->clip_enabled ? app->clip_min[1] : 0.0f,
                     app->clip_enabled ? app->clip_min[2] : 0.0f, 0.0f};
  params.clip_max = {app->clip_enabled ? app->clip_max[0] : 1.0f,
                     app->clip_enabled ? app->clip_max[1] : 1.0f,
                     app->clip_enabled ? app->clip_max[2] : 1.0f, 0.0f};
  params.settings0 = {value_offset, value_scale, app->density_gain, app->value_gamma};
  params.settings1 = {app->opacity_power, std::tan(kCameraFovYRadians * 0.5f),
                      app->path_trace_sun_angle, app->path_trace_sun_azimuth};
  params.settings2 = {app->path_trace_sun_strength, app->path_trace_sky_strength,
                      app->path_trace_albedo,
                      static_cast<float>(app->path_trace_completed_passes)};
  params.settings_i0 = {app->path_trace_width, app->path_trace_height,
                        std::max(1, std::min(512, app->sample_steps)),
                        app->invert_values ? 1 : 0};
  params.settings_i1 = {volume.dim[0], volume.dim[1], volume.dim[2], 0};
  params.settings_i2 = {app->slice_axis, 0, 0, 0};
  params.settings3 = {app->slice_pos, app->slice_axis ? app->slice_thickness : 1.0f,
                      0.0f, 0.0f};
  std::memcpy(backend->params.mapped, &params, sizeof(params));

  backend->vk.ResetFences(backend->device, 1, &backend->fence);
  backend->vk.ResetCommandBuffer(backend->command_buffer, 0);
  VkCommandBufferBeginInfo begin = {};
  begin.sType = VK_STRUCTURE_TYPE_COMMAND_BUFFER_BEGIN_INFO;
  if (!VkOk(backend->vk.BeginCommandBuffer(backend->command_buffer, &begin),
            "vkBeginCommandBuffer", backend)) {
    return false;
  }
  backend->vk.CmdBindPipeline(backend->command_buffer, VK_PIPELINE_BIND_POINT_COMPUTE,
                              backend->pipeline);
  backend->vk.CmdBindDescriptorSets(backend->command_buffer, VK_PIPELINE_BIND_POINT_COMPUTE,
                                    backend->pipeline_layout, 0, 1,
                                    &backend->descriptor_set, 0, nullptr);
  backend->vk.CmdDispatch(backend->command_buffer,
                          static_cast<uint32_t>((app->path_trace_width + 7) / 8),
                          static_cast<uint32_t>((app->path_trace_height + 7) / 8), 1);
  if (!VkOk(backend->vk.EndCommandBuffer(backend->command_buffer), "vkEndCommandBuffer",
            backend)) {
    return false;
  }
  VkSubmitInfo submit = {};
  submit.sType = VK_STRUCTURE_TYPE_SUBMIT_INFO;
  submit.commandBufferCount = 1;
  submit.pCommandBuffers = &backend->command_buffer;
  if (!VkOk(backend->vk.QueueSubmit(backend->queue, 1, &submit, backend->fence),
            "vkQueueSubmit", backend)) {
    return false;
  }
  backend->vk.WaitForFences(backend->device, 1, &backend->fence, VK_TRUE, UINT64_MAX);
  const std::size_t bytes =
      static_cast<std::size_t>(app->path_trace_width) * app->path_trace_height * 4;
  app->path_trace_rgba.resize(bytes);
  const uint8_t* src = reinterpret_cast<const uint8_t*>(backend->rgba.mapped);
  for (std::size_t i = 0; i < bytes / 4; ++i) {
    app->path_trace_rgba[i * 4 + 0] = src[i * 4 + 0];
    app->path_trace_rgba[i * 4 + 1] = src[i * 4 + 1];
    app->path_trace_rgba[i * 4 + 2] = src[i * 4 + 2];
    app->path_trace_rgba[i * 4 + 3] = src[i * 4 + 3];
  }
  glBindTexture(GL_TEXTURE_2D, app->path_trace_texture);
  glPixelStorei(GL_UNPACK_ALIGNMENT, 1);
  glTexSubImage2D(GL_TEXTURE_2D, 0, 0, 0, app->path_trace_width,
                  app->path_trace_height, GL_RGBA, GL_UNSIGNED_BYTE,
                  app->path_trace_rgba.data());
  ++app->path_trace_completed_passes;
  app->path_trace_next_row = 0;
  app->path_trace_last_backend = "vulkan-compute";
  return true;
}
#else
void DestroyVulkanPathTrace(AppState*) {}
bool InitVulkanPathTrace(AppState*) { return false; }
bool UpdatePathTraceVulkan(AppState*) { return false; }
#endif
