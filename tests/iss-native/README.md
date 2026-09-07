# Native ISS fixtures

`reverse_rows.loop` and `reverse_columns.loop` are local matrix extensions of
Pluto's `reverse-iss` example. The one-dimensional source is under
`tests/end-to-end-c/cases/reverse_iss/`. `run_native_iss_suite.py` checks the
three inputs under five configurations; configurations are not extra kernels.

## Periodic Jacobi

The periodic fixtures adapt the computation regions of Pluto's
`test/jacobi-1d-periodic.c` and `test/jacobi-2d-periodic.c`. They retain the two
physical buffers, periodic boundary accesses, update multiplicities, and time
order. They do not replace alternating buffers with full-time storage.

The `phase` inputs express time as `t = 2*q + p + 1`, where `p` is zero or one.
The guard `t < T` removes the final unused phase. Thus the destination buffer
is `1-p`, and the source buffer is `p`; all access indices are affine. Pluto
actually splits this phase coordinate, and the generated loops separate the
two buffer-update phases. These are genuine ISS proposals, but not the spatial
midpoint cuts chosen by PET for the original C representation.

Two alternative one-dimensional representations are retained for diagnosis:

- `guards` spells out the boundary cases as separate statements. In the tested
  configuration, Pluto cuts at `-p-1=0` although `p` is zero or one. Each
  statement therefore gains an empty piece, without separating its nonempty
  phase regions. This representation is not counted as producing that effect.
- `quotient` represents `t % 2` by an additional bounded quotient iterator.
  Pluto does not split it in the tested native configuration.

These alternatives are not additional benchmarks. The additions are two
distinct kernels: periodic Jacobi in one and two spatial dimensions.

`SInstr` conservatively includes reads from both branches of a conditional
expression in its access summary. The `phase` representation therefore has
the same executed physical accesses as the C computation, but a larger static
read summary than PET's piecewise accesses. No frontend semantics or proof is
changed by these fixtures.

## Checks

Run `tools/iss/run_periodic_iss_suite.py` against an already-built tree. It
captures actual Pluto inputs and ISS witnesses, checks that the split is
forwarded, and compiles a complete-execution observer for the original C
computation, adapted input, and final generated loop. The observer compares:

- every selected physical read and the version of the value read;
- the number of writes to each cell and both final buffers;
- separation of the two nonempty phase regions at final assignment sites.

The one-dimensional suite uses 114 parameter pairs; the two-dimensional suite
uses 98. Both include empty and singleton domains, tile boundaries, and multiple
buffer reuses. Large-time samples use zero initial values to avoid machine
overflow; their access-version checks remain active. These are complete
executions at bounded parameter values, not an exhaustive correctness proof.

`test_periodic_iss_harness.py` checks the observer itself against wrong-buffer,
wrong-boundary, missing-update, duplicate-execution, and wrong-diagonal mutations.
`run_phase_iss_adapter_tests.py` separately checks candidate reconstruction and
the unchanged extracted complete-cut checker, including invalid partitions and
instruction/access payload changes.
