This test tries to validate all example transformations in pluto's repo.

For each example:
1. it runs pluto on the `.c` file, generating two openscop, for before and after scheduling each.
   1. run pluto with `--dumpscop --nointratileopt --nodiamond-tile --noprevector --smartfuse --nounrolljam --noparallel --notile --rar`
2. it reads the two openscop file to polyhedral models, omitting the actual instruction (supposing the access function overapproximate instruction's dynamic semantics)
3. run validate on two models (bidirectionally), produce output

Note that, validator's algorithm only guarantee "all WR/WW dependences have same directions" for two polyhedral models. Invoking the validator without verifying the instruction-language's semantics, leaving the following reponsibility to the user:
1. Checking that read/write access functions are correct to each instruction's semantics.
2. Certifying that no memory cells can alias each other with different identifier or index lists (for `a[i][j]` and `i=0, j=1`, the memory cell for the access is `a[1][1]`, `a` the identifier, `[1;1]` the access list. Different memory cell (for `a[1][1]` and `a[2][0]`, index overflow may lead to aliasing; for `a` and `b`, identifier alias may cause aliasing; many other cases) should not alias each other). 
