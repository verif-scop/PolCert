# Original OpenScop Batch Examples

These examples exercise standalone affine validation on Pluto-generated
OpenScop pairs. They predate the complete loop compiler; use
[Testing](../../doc/TESTING.md) for the maintained regression entry points.

The affine-only producer recipe is:

```sh
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector \
  --smartfuse --nounrolljam --noparallel --notile --rar example.c
```

Run it in a scratch directory containing the input. Check the resulting
before/after pair with `polcert`, as described in
[Standalone Validation](../../POLCERT.md). The original scripts can check
both directions; the compiler contract itself requires target-to-source
refinement.

The importer omits instruction bodies and relies on the supplied access
summaries. It checks potential write/write, write/read, and read/write
conflicts under changed schedules. Users of this standalone interface must
justify those summaries and the memory model, including aliasing and overflow.
An accepted OpenScop pair alone is not a C-program equivalence result.
