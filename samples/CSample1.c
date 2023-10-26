// matmul, matrix multiplication
// Link to examples to pluto's examples: https://github.com/bondhugula/pluto/blob/eddc38537d61cd49d55e454831086848d51473d7/examples/matmul/matmul.c#L69

#pragma scop
  for (i = 0; i < M; i++)
    for (j = 0; j < N; j++)
      for (k = 0; k < K; k++)
        C[i][j] = beta * C[i][j] + alpha * A[i][k] * B[k][j];
#pragma endscop


// afterscheduling:
// for (k = 0; k < K; k++)
//   for (j = 0; j < N; j++)
//     for (i = 0; i < M; i++)
//       C[i][j] = C[i][j] + A[i][k] * B[k][j];

// Note:
// 1. speed-up is not in our concern, but with only "reordering", programs are possible to gain significant speed-up in our working setting, concretely for sample2/3.
// 2. validator works bidirectionally for all sample1/2/3, which suggests they are semantically equivalent (not just refinement).
