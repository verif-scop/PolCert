# Affine Scheduling Samples

These small examples pair C loop kernels with polyhedral models in Rocq:

| Sample | Computation | Scheduling example |
| --- | --- | --- |
| `CSample1` | Matrix multiplication | Loop interchange |
| `CSample2` | Column covariance | Loop distribution |
| `CSample3` | Matrix/vector computation | Statement fusion |

They illustrate the affine validator. For the complete compiler, start with
[polopt](../POLOPT.md) and the [loop examples](../syntax/examples).

To regenerate affine-only OpenScop exports, copy a C sample into a scratch
directory and run:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
  --smartfuse --nounrolljam --noparallel --notile --rar CSample1.c
```

This sample recipe explicitly requests `--rar`; it is not the default PolCert
producer policy. Pluto writes before/after OpenScop models and code-generation
files. The models omit the Rocq instruction-typing information, so their
standalone validation relies on the access-summary assumptions explained in
[polcert](../POLCERT.md).

Generated code and timings depend on the selected producer and machine.
These samples do not provide current performance measurements.
