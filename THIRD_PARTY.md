# Third-party material

Source headers retain the applicable authorship and copyright notices.
PolCert's [LICENSE](LICENSE) does not replace licenses of bundled components.

| Material | Location | License |
| --- | --- | --- |
| CompCert-derived infrastructure | `common/`, `cfrontend/`, `cparser/`, `lib/`, architecture directories | [LICENSE](LICENSE) and file headers |
| Verified Polyhedra Library | `VPL/` | [VPL/LICENSE](VPL/LICENSE) |
| Flocq | `flocq/` | File headers and [LGPL-3.0](licenses/LGPL-3.0.txt) |
| MenhirLib | `MenhirLib/` | File headers and [LGPL-3.0](licenses/LGPL-3.0.txt) |
| Pluto-derived benchmark inputs | `tests/`, `evaluation/inputs/` | [Pluto MIT license](licenses/Pluto-MIT.txt) and source notices |

Evaluation manifests record the original loop-corpus path for each kernel.
Content-addressed filenames preserve the experiment input bytes. Supplementary
examples retain any additional attribution in their source comments.
Pluto itself and its dependencies are fetched at pinned commits by the
Dockerfile; their licenses remain in their respective checkouts.
