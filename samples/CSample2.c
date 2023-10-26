// covcol, convariance calculation
// Link to examples to pluto's examples: https://github.com/bondhugula/pluto/blob/eddc38537d61cd49d55e454831086848d51473d7/examples/covcol/covcol.c#L97

#pragma scop
  /* Calculate the m * m covariance matrix. */
  for (j1 = 1; j1 <= M; j1++) {
    for (j2 = j1; j2 <= M; j2++) {
      for (i = 1; i <= N; i++) {
        symmat[j1][j2] += data[i][j1] * data[i][j2];
      }
      symmat[j2][j1] = symmat[j1][j2];
    }
  }
#pragma endscop

// afterscheduling: 
// for (i = 1; i <= N; i++) {
//   for (j1 = 1; j1 <= M; j1++) {
//     for (j2 = j1; j2 <= M; j2++) {
//       symmat[j1][j2] += data[i][j1] * data[i][j2];
//     }
//   }
// }
// for (j1 = 1; j1 <= M; j1++) {
//   for (j2 = j1; j2 <= M; j2++) {
//     symmat[j2][j1] = symmat[j1][j2];
//   }
// }

// Note:
// 1. speed-up is not in our concern, but with only "reordering", programs are possible to gain significant speed-up in our working setting, concretely for sample2/3.
// 2. validator works bidirectionally for all sample1/2/3, which suggests they are semantically equivalent (not just refinement).
