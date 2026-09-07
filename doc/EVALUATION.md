# Evaluation

The manual experiments in [`evaluation/`](../evaluation) measure whether
PolCert retains Pluto's optimization effects and how much compilation time the
verified pipeline adds. Historical miscompilation checks are separate
[regression tests](TESTING.md).

## Optimization retention

Each manifest pairs a loop kernel with an optimization configuration. The
collector runs Pluto and PolCert, saves their outputs, and observes the
requested effect. Compiler acceptance alone does not count as retaining an
effect: a configuration must first produce that effect in Pluto, and the
corresponding PolCert output must preserve it.

Inside the built development environment, run a small selection first:

```sh
python3 evaluation/bin/run_evaluation.py retention \
  --cohort primary-rectangular --kernel matmul \
  --output /tmp/polcert-retention-matmul
```

Omit `--kernel` to run the selected cohort, or omit both selectors to run the
whole plan. `evaluation/manifests/plan.json` lists the cohorts, input manifests,
and collection parameters. Inputs come from the loop corpus, Pluto tests,
and supplementary polyhedral examples.

The output contains the collection commands, source and executable hashes,
raw proposals, generated loops, and effect observations. Inspect unresolved
observations before aggregating results; successful collection is not itself
an effect-retention result. Parallel comparisons include group membership,
because a nontrivial parallel loop alone need not preserve Pluto's group.

## Compilation overhead

```sh
python3 evaluation/bin/run_evaluation.py timing \
  --kernel 1dloop-invar --kernel dct \
  --output /tmp/polcert-timing-small
```

The timing manifest uses a common compilation configuration across its
kernels. It is distinct from the per-effect retention configurations.
The collector measures complete Pluto and PolCert processes over three
repetitions. An isolated instrumented build breaks down PolCert's time by
stage and separates VPL solving from construction of validation queries.
It does not overwrite the ordinary compiler executable.

Measurements and summaries report seconds. Keep absolute time differences
alongside ratios: ratios alone exaggerate overhead for very short baseline
compilations. Inspect the dominant stages of slow kernels before attributing
their cost to validation. A timed-out compilation is recorded as such, not as
a successful measurement.

## Running and maintaining experiments

Use a fresh output directory outside `evaluation/`; repeated commands never
overwrite previous results. Run timing experiments without concurrent builds
or other measurements. The collector records executable hashes and commands
so results can be associated with the tested version.

These experiments are not part of default CI. The development repository
contains their scripts, inputs, and configurations, but no frozen publication
results. Published evidence remains in the corresponding release package.
