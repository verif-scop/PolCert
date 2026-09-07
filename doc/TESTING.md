# Testing

The proof build establishes the formal results. Regression tests additionally
exercise extraction, command-line dispatch, serialization, external optimizer
interfaces, and executable outputs.

## Complete validation

From a clean checkout:

```sh
docker build --target ci -t polcert-ci .
bash tools/ci/run_ci_shards.sh polcert-ci
```

The image build compiles all proofs, runs the open-proof gate, extracts OCaml,
and builds `polcert` and `polopt`. The shard runner exercises the same checks
as the default GitHub workflow. Any nonzero shard exit fails the run.

## Focused checks

Run these inside the development container after building the tools:

| Area | Command |
| --- | --- |
| Legacy and frontend regressions | `make test` |
| Quick aggregate regression suite | `make check-smoke` |
| Integer constraint normalization | `make test-affine-integer-fastpath` |
| Direct tiling validation | `make test-direct-only-tiling-routes` |
| Two-level tiling | `make test-second-level-tile-suite` |
| Diamond tiling | `make test-diamond-tiling-suite` |
| Parallel loop generation | `make test-parallel-current-suite` |
| Statement-scoped hints | `make test-parallel-scope` |
| Tiled instruction round trips | `make test-tiling-body-roundtrip` |
| Vector annotations | `make test-vector-current-suite` |
| ISS with Pluto | `make test-iss-pluto-suite test-iss-pluto-live-suite` |
| Pluto-style options | `make test-pluto-compat-suite` |
| Generated loop corpus | `make test-polopt-loop-suite` |
| Executable C comparisons | `make test-end-to-end-c-correctness` |
| Historical optimizer defects and fixed-producer regressions | `make test-pluto-bugs` |

The manifests under `tests/` define the accepted route, rejection, and output
requirements. Acceptance alone is not an optimization-effect check. Where
relevant, tests inspect nontrivial loop structure or compare complete final
array states against the source execution.

## Historical compiler tests

`tools/pluto_bugs/` selects the pinned historical compiler through
`POLCERT_BUGGY_ROOT`; fixed-producer checks use the ordinary Pluto path.
Fixture READMEs explain the violated dependence or annotation condition.
The inner-parallel regression permits safe singleton parallel loops and checks
their execution, rather than requiring one particular generated schedule.

## Manual experiments

[Evaluation](EVALUATION.md) describes optimization-retention comparisons,
end-to-end compilation timing, and stage profiling. These measurements are
separate from default CI. Run them without concurrent compilation or other
benchmark workloads, and keep their commands, revisions, and raw results.
