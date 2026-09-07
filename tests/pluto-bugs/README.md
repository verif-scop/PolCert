# Pluto correctness regressions

These tests reproduce invalid optimizer results and check PolCert's response.
They also check repairs in the fixed producer. Run them with:

```sh
opam exec -- make test-pluto-bugs
```

## Historical miscompilations

The following cases use the pinned historical Pluto at
`POLCERT_BUGGY_ROOT` (default `/opt/polcert/pluto-buggy`). A missing or mismatched
historical checkout is an error.

| Fixture | Failure checked |
| --- | --- |
| [auto-affine-lp-cc-scaling](auto-affine-lp-cc-scaling/README.md) | LP integerization scales the two ends of a dependence inconsistently. |
| [tiling-innerpar-satvec](tiling-innerpar-satvec/README.md) | Dependence metadata permits an unsafe parallel hint after legal tiling. |
| [vanished-outer-parallel](vanished-outer-parallel/README.md) | Elimination of a singleton loop transfers its parallel annotation to a dependent inner loop. |
| [notile-unrolljam-nonpermutable](notile-unrolljam-nonpermutable/README.md) | Unroll-and-jam crosses a nonpermutable band. |
| [tiling-mixed-depth-cross-band](tiling-mixed-depth-cross-band/README.md) | Tiling moves a copy before a dependent standalone write. |

The separate [affine-fst-reversed](affine-fst-reversed/README.md) case supplies
an inconsistent control file. It checks rejection of an illegal requested
schedule, not an automatically discovered optimization.

## Fixed producer and interface checks

[diamond-nointratile-reschedule](diamond-nointratile-reschedule/README.md)
checks legal intermediate exports and matching complete array states with
RAR both disabled and enabled. The matmul hint test checks raw-to-canonical
coordinate mapping and the resulting nontrivial parallel loop. These tests
use the ordinary fixed Pluto checkout, not the historical compiler.

[`tools/ci/check_pluto_baseline.sh`](../../tools/ci/check_pluto_baseline.sh)
checks both revisions. Ordinary optimizer tests always use fixed Pluto.
ISS adversarial fixtures are in [iss-pluto-dumps](../iss-pluto-dumps/README.md);
inconsistent split-domain metadata is not automatically classified as an
executable numerical miscompilation.
