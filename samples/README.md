You can generate openscop file for samples with:

```
pluto --dumpscop --nointratileopt --nodiamond-tile --noprevector --smartfuse --nounrolljam --noparallel --notile --rar CSample[123].c
```

They should carry semantically equivalent information (except the typing information of instructions) with the polyhedral model in CSample[123].v.  

Pluto also generates *.pluto.cloog for cloog (the code generator, from polyhedra to C source) special format (should be equivalent to *.afterscheduling.scop), and *.pluto.c for final c code generated by cloog. They are not used in this project, but can help with better understanding.

Though speed-up is not in our concern, we do empirical tests (https://github.com/verif-scop/speed-up) on local machine (use these three samples) to see the supporting optimization potential, it shows that csample1 suffers slowing down, but csample2/3 gains significant speed-up (x2-x8). You can try on your own machine.

# Samples

Sample1: matmul. Scheduling: The outer and inner loop is flipped.

Sample2: covcol. Scheduling: The second layer is unfused (two instructions).

Sample3: gemver. Scheduling: Four instructions are fused.
