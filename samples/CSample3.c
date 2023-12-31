// gemver, Vector Multiplication and Matrix Addition
// Link to examples to pluto's examples: https://github.com/bondhugula/pluto/blob/eddc38537d61cd49d55e454831086848d51473d7/examples/gemver/gemver.c#L81

#pragma scop
    for (i=0; i<N; i++)
        for (j=0; j<N; j++)
            B[i][j] = A[i][j] + u1[i]*v1[j] + u2[i]*v2[j];

    for (i=0; i<N; i++)
        for (j=0; j<N; j++)
            x[i] = x[i] + beta* B[j][i]*y[j];


    for (i=0; i<N; i++)
        x[i] = x[i] + z[i];

    for (i=0; i<N; i++)
        for (j=0; j<N; j++)
            w[i] = w[i] + alpha* B[i][j]*x[j];
#pragma endscop
