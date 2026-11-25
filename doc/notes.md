# Notes, license and third-party licenses

> Extracted from the [TinyVDB README](../README.md) for detailed reference.

## Notes

### Terms

`background` is a uniform constant value used when there is no voxel data.

`Node` is composed of Root, Internal, and Leaf.
Leaf contains actual voxel data.

Root and Internal nodes have `Value` or a pointer to a child node, where `Value` is a constant value for the node.

There are two bit masks, `child mask` and `value mask`, for each internal node.

## License

TinyVDB is licensed under the [Apache License, Version 2.0](http://www.apache.org/licenses/LICENSE-2.0).

```
Copyright 2026 - Present Syoyo Fujita

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```

### Third party licenses

| Library | License |
|---------|---------|
| OpenVDB (original I/O logic) | Apache 2.0 |
| LZ4 | BSD 2-Clause |
| miniz | MIT |
| tinyexr (vdbrender example) | BSD 3-Clause |
