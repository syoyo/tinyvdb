#include <cstdio>
#include <cstdlib>

#include "simple_vtk.hpp"

#define TINYVDB_IO_IMPLEMENTATION
#include "tinyvdb_io.h"

struct Extent
{
  std::array<double, 3> bmin;
  std::array<double, 3> bmax;
};

int main(int argc, char **argv)
{
  if (argc < 3) {
    std::cout << argv[0] << " input.vdb output.vtki\n";
    return EXIT_FAILURE;
  }

  std::string input_filename = argv[1];
  std::string output_filename = argv[2];

  // 1. Parse VDB header
  tinyvdb::VDBHeader header;
  std::string warn;
  std::string err;
  tinyvdb::VDBStatus status = tinyvdb::ParseVDBHeader(input_filename, &header, &err);

  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << err << std::endl;
    }
    return EXIT_FAILURE;
  }

  // 2. Read Grid descriptors
  std::map<std::string, tinyvdb::GridDescriptor> gd_map;

  status = tinyvdb::ReadGridDescriptors(input_filename, header, &gd_map, &err);
  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << err << std::endl;
    }
    return EXIT_FAILURE;
  }

  std::cout << "# of grid descriptors = " << gd_map.size() << std::endl;

  status = tinyvdb::ReadGrids(input_filename, header, gd_map, &warn, &err);
  if (!warn.empty()) {
    std::cout << warn << std::endl;
  }
  if (status != tinyvdb::TINYVDBIO_SUCCESS) {
    if (!err.empty()) {
      std::cerr << err << std::endl;
    }
    return EXIT_FAILURE;
  }

  for (const auto &desc : gd_map) {
    std::cout << "name: " << desc.second.GridName() << "\n"; 
  }

  std::array<double, 3> origin{};
  std::array<double, 3> spacing{};

  Extent extent;

  SimpleVTK gen;
  gen.enableExtentManagement();
  gen.changeBaseExtent(extent.bmin[0], extent.bmax[0], extent.bmin[1], extent.bmax[1], extent.bmin[2], extent.bmax[2]);
  gen.changeBaseOrigin(origin[0], origin[1], origin[2]);
  gen.changeBaseSpacing(spacing[0], spacing[1], spacing[2]);
  gen.changeRefinementRatio(2.0);

  gen.beginVTK("vtkHierarchicalBoxDataSet");
  gen.beginContent();
  gen.setGridDescription("XYZ");

  gen.endContent();
  gen.endVTK();

  gen.generate("output_amr");

  return EXIT_SUCCESS;

}
