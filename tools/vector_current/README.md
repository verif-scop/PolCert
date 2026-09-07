# Vector Coordinate Regressions

Vector certificates use canonical schedule coordinates, as parallel certificates
do. For `positive.loop`, the tiled schedule is
`[floor(i/32), floor(j/32), i, j]`. The explicit innermost request is therefore
`--vector-current 3`. Coordinate 2 denotes the outer point loop `i` and must fail
the innermost gate. The former acceptance of 2 reflected cleanup-time physical
depth, not this schedule contract.

The final program has only three nested loops because `0 <= j < 4` makes its
tile coordinate constant. Tests require a vectorized innermost `j` loop after
that cleanup; they do not depend on the printer's iterator names.

Run the explicit-coordinate checks and real hinted checks from a built tree:

```sh
python3 tools/vector_current/run_vector_current_suite.py --polopt ./polopt
python3 tools/vector_current/run_hinted_vector_suite.py --polopt ./polopt --pluto /path/to/pluto
python3 -m unittest discover -s tools/vector_current -p 'test_*.py'
make test-parallel-hint-mapping
```

The hinted suite runs existing positive, symbolic identity, symbolic two-level,
and dependent fixtures. Its positive-default case checks the actual four-row
Pluto proposal, three final loop levels, the innermost vector annotation, all
400 writes, final values, and that vector lanes correspond to `j`. Repeating
that case with a missing or misleading C sidecar must produce identical final
Loop text. Matrix cases check the vector coordinate and complete executions on
eight parameter pairs, including tile boundaries. The dependent case must
remain unvectorized. Exit code 0 without these effects does not pass the suite.

The mapping tests separately call `run_pluto_scop_with_vector_hint` with missing,
malformed, and misleading C sidecars. They cover both a retained scalar schedule
row and a globally zero row removed by canonicalization.
