(* 
Sample3: gemver.c
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
*)

(*
# [File generated by the OpenScop Library 0.9.2]

<OpenScop>

# =============================================== Global
# Language
C

# Context
CONTEXT
0 3 0 0 0 1

# Parameters are provided
1
<strings>
N
</strings>
*)
(*
# Number of statements
4
*)
Require Import PolyBase.
Require Import List.
Import List.ListNotations.
Require Import ZArith.
Require Import CPolIRs.
Open Scope Z_scope.

(** Instruction 1: B[i][j] = A[i][j] + u1[i]*v1[j] + u2[i]*v2[j]; *)
(* Domain: 
# ----------------------------------------------  1.1 Domain
DOMAIN
5 5 2 0 0 1
# e/i|  i    j |  N |  1  
   1    1    0    0    0    ## i >= 0
   1   -1    0    1   -1    ## -i+N-1 >= 0
   1    0    0    1   -1    ## N-1 >= 0
   1    0    1    0    0    ## j >= 0
   1    0   -1    1   -1    ## -j+N-1 >= 0
*)
Definition sample_domain1: Domain := [
    (** N | i j | const *)
    (** 1. -i <= 0 (i >= 0) *)
    ([0; -1; 0], 0);
    (** 2. i-N<=-1 (i<=N-1) *)
    ([-1; 1; 0], -1);
    (** 3. N - 1 >= 0 (-N <= -1)*)
    ([-1; 0; 0], -1);
    (** 4. j >= 0 (-j <= 0) *)
    ([0; 0; -1], 0);
    (** 5. j <= N - 1 (-j+N-1 >= 0) *)
    ([-1; 0; 1], -1)
].

(*
# ----------------------------------------------  1.2 Scattering
SCATTERING
5 10 5 2 0 1
# e/i| c1   c2   c3   c4   c5 |  i    j |  N |  1  
   0   -1    0    0    0    0    0    0    0    0    ## c1 == 0
   0    0   -1    0    0    0    1    0    0    0    ## c2 == i
   0    0    0   -1    0    0    0    0    0    0    ## c3 == 0
   0    0    0    0   -1    0    0    1    0    0    ## c4 == j
   0    0    0    0    0   -1    0    0    0    0    ## c5 == 0
*)

(** (0, i, 0, j, 0) *)
Definition sample_sctt1: AffineFunction := [
    ([ 0; 0; 0], 0);
    ([ 0; 1; 0], 0);
    ([ 0; 0; 0], 0);
    ([ 0; 0; 1], 0);
    ([ 0; 0; 0], 0)
].

(* 
# ----------------------------------------------  1.3 Access
WRITE
3 8 3 2 0 1
# e/i| Arr  [1]  [2]|  i    j |  N |  1  
   0   -1    0    0    0    0    0    4    ## Arr == B
   0    0   -1    0    1    0    0    0    ## [1] == i
   0    0    0   -1    0    1    0    0    ## [2] == j
*)

Definition sample_waccess1: list AccessFunction := (
    (** B[i][j] *)
    4%positive, 
    [
        (** N | i j *)
        ([0; 1; 0], 0);
        ([0; 0; 1], 0)
    ]
)::nil.

(*
READ
3 8 3 2 0 1
# e/i| Arr  [1]  [2]|  i    j |  N |  1  
   0   -1    0    0    0    0    0    5    ## Arr == A
   0    0   -1    0    1    0    0    0    ## [1] == i
   0    0    0   -1    0    1    0    0    ## [2] == j

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0    6    ## Arr == u1
   0    0   -1    1    0    0    0    ## [1] == i

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0    7    ## Arr == v1
   0    0   -1    0    1    0    0    ## [1] == j

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0    8    ## Arr == u2
   0    0   -1    1    0    0    0    ## [1] == i

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0    9    ## Arr == v2
   0    0   -1    0    1    0    0    ## [1] == j
*)

Definition sample_raccess1: list AccessFunction := [
    (
        (** A[i][j] *)
        5%positive, 
        [
            (** N | i j *)
            ([0; 1; 0], 0);
            ([0; 0; 1], 0)
        ]
    );
    (
        (** u1[i] *)
        6%positive, 
        [
            (** N | i j *)
            ([0; 1; 0], 0)
        ]
    );
    (
        (** v1[j] *)
        7%positive, 
        [
            (** M N K | i j k *)
            ([0; 0; 1], 0)
        ]
    );
    (
        (** u2[i] *)
        8%positive, 
        [
            (** N | i j *)
            ([0; 1; 0], 0)
        ]
    );
    (
        (** v2[j] *)
        9%positive, 
        [
            (** N | i j *)
            ([0; 0; 1], 0)
        ]
    )
].

(* transformation is set as identity *)
Definition sample_transformation1 := [
    ([1; 0; 0], 0);
    ([0; 1; 0], 0);
    ([0; 0; 1], 0)
].

(*
<body>
# Number of original iterators
3
# List of original iterators
i j k
# Statement body expression
C[i][j] = beta * C[i][j] + alpha * A[i][k] * B[k][j];
</body>
*)
Require Import CTy.

(* M(2) N(4) K(6) i(1) j(3) k(5), nat 0-5*)
(*
<arrays>
# Number of arrays
15
# Mapping array-identifiers/array-names
2 N (0)
1 i (1)
3 j (2)
4 B, 5 A, 6 u1
7 v1, 8 u2   , 9 v2
10 x, 11 beta, 12 y
13 z, 14 w,    15 alpha
</arrays>
*)

(*B[i][j] = A[i][j] + u1[i]*v1[j] + u2[i]*v2[j];*)
Definition sample_cinstr1 := 
    CPolIRs.Instr.Iassign 
        (* B[i][j] *)
        (CPolIRs.Instr.Aarr 
            4%positive 
            (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 1%nat) 
                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)))
            CTy.int32s
        )
        (CPolIRs.Instr.Ebinop
            Cop.Oadd
                (* A[i][j] *)
                (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 
                          5%positive 
                          (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 1%nat) 
                              (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)))
                            CTy.int32s
                      ) CTy.int32s)
                (* u1[i]*v1[j] + u2[i]*v2[j] *)
                (CPolIRs.Instr.Ebinop Cop.Oadd
                    (* u1[i]*v1[j] *)
                    (CPolIRs.Instr.Ebinop Cop.Omul
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 6%positive 
                            (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat))
                            CTy.int32s) CTy.int32s)
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 7%positive 
                              (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)) CTy.int32s)
                              CTy.int32s) CTy.int32s)
                    (* u2[i]*v2[j] *)
                    (CPolIRs.Instr.Ebinop Cop.Omul
                    (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 8%positive 
                        (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat))
                        CTy.int32s) CTy.int32s)
                    (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 9%positive 
                          (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)) CTy.int32s)
                        CTy.int32s) CTy.int32s)
                    CTy.int32s                    
                  )
            CTy.int32s
        )
.

(** Instruction 2, x[i] = x[i] + beta* B[j][i]*y[j]; *)
(* Domain 2:
# ----------------------------------------------  2.1 Domain
DOMAIN
5 5 2 0 0 1
# e/i|  i    j |  N |  1  
   1    1    0    0    0    ## i >= 0
   1   -1    0    1   -1    ## -i+N-1 >= 0
   1    0    0    1   -1    ## N-1 >= 0
   1    0    1    0    0    ## j >= 0
   1    0   -1    1   -1    ## -j+N-1 >= 0
*)

Definition sample_domain2 := [
    (** N | i j | const *)
    (** 1. -i <= 0 (i >= 0) *)
    ([0; -1; 0], 0);
    (** 2. i-N<=-1 (i<=N-1) *)
    ([-1; 1; 0], -1);
    (** 3. N - 1 >= 0 (-N <= -1)*)
    ([-1; 0; 0], -1);
    (** 4. j >= 0 (-j <= 0) *)
    ([0; 0; -1], 0);
    (** 5. j <= N - 1 (-j+N-1 >= 0) *)
    ([-1; 0; 1], -1)
].


(*
# ----------------------------------------------  2.2 Scattering
SCATTERING
5 10 5 2 0 1
# e/i| c1   c2   c3   c4   c5 |  i    j |  N |  1  
   0   -1    0    0    0    0    0    0    0    1    ## c1 == 1
   0    0   -1    0    0    0    1    0    0    0    ## c2 == i
   0    0    0   -1    0    0    0    0    0    0    ## c3 == 0
   0    0    0    0   -1    0    0    1    0    0    ## c4 == j
   0    0    0    0    0   -1    0    0    0    0    ## c5 == 0
*)

(** (0, i, 0, j, 0) *)
Definition sample_sctt2: AffineFunction := [
    ([ 0; 0; 0], 1);
    ([ 0; 1; 0], 0);
    ([ 0; 0; 0], 0);
    ([ 0; 0; 1], 0);
    ([ 0; 0; 0], 0)
].


(* 
# ----------------------------------------------  2.3 Access
WRITE
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   10    ## Arr == x
   0    0   -1    1    0    0    0    ## [1] == i
*)

Definition sample_waccess2: list AccessFunction := (
    (** x[i] *)
    10%positive, 
    [
        (** N | i j *)
        ([0; 1; 0], 0)
    ]
)::nil.

(*
READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   10    ## Arr == x
   0    0   -1    1    0    0    0    ## [1] == i

READ
1 6 1 2 0 1
# e/i| Arr|  i    j |  N |  1  
   0   -1    0    0    0   11    ## Arr == beta

READ
3 8 3 2 0 1
# e/i| Arr  [1]  [2]|  i    j |  N |  1  
   0   -1    0    0    0    0    0    4    ## Arr == B
   0    0   -1    0    0    1    0    0    ## [1] == j
   0    0    0   -1    1    0    0    0    ## [2] == i

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   12    ## Arr == y
   0    0   -1    0    1    0    0    ## [1] == j
*)

Definition sample_raccess2: list AccessFunction := [
    (
        (** x[i] *)
        10%positive, 
        [
            (** N | i j *)
            ([0; 1; 0], 0)
        ]
    );
    (
        (** beta *)
        11%positive, 
        [
            (** N | i j *)
        ]
    );
    (
        (** B[j][i] *)
        4%positive, 
        [
            (** N | i j *)
            ([0; 0; 1], 0);
            ([0; 1; 0], 0)
        ]
    );
    (
        (** y[j] *)
        12%positive, 
        [
            (** N | i j *)
            ([0; 0; 1], 0)
        ]
    )
].

(* transformation is set as identity *)
Definition sample_transformation2 := [
    ([1; 0; 0], 0);
    ([0; 1; 0], 0);
    ([0; 0; 1], 0)
].

(*
<arrays>
# Number of arrays
15
# Mapping array-identifiers/array-names
2 N (0)
1 i (1)
3 j (2)
4 B, 5 A, 6 u1
7 v1, 8 u2   , 9 v2
10 x, 11 beta, 12 y
13 z, 14 w,    15 alpha
</arrays>
*)

(* x[i] = x[i] + beta* B[j][i]*y[j]; *)
Definition sample_cinstr2 := 
    CPolIRs.Instr.Iassign 
        (* x[i] *)
        (CPolIRs.Instr.Aarr 
            10%positive  
              (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat))
            CTy.int32s
        )
        (CPolIRs.Instr.Ebinop
            Cop.Oadd
                (* x[i] *)
                (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 10%positive  
                  (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat)) CTy.int32s ) CTy.int32s)
                (* beta* B[j][i]*y[j] *)
                (CPolIRs.Instr.Ebinop Cop.Omul
                    (* beta *)
                      (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Avar 11%positive CTy.int32s)
                      CTy.int32s) 
                    (* B[j][i]*y[j]*)
                    (CPolIRs.Instr.Ebinop Cop.Omul
                    (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 4%positive 
                      (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 2%nat)
                        (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat)))
                        CTy.int32s) CTy.int32s)
                      (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 12%positive  
                        (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)) CTy.int32s ) CTy.int32s) CTy.int32s)
                    CTy.int32s                    
                  )
            CTy.int32s
        )
.



(** Instruction 3: x[i] = x[i] + z[i]; *)
(* Domain 
# ----------------------------------------------  3.1 Domain
DOMAIN
3 4 1 0 0 1
# e/i|  i |  N |  1  
   1    1    0    0    ## i >= 0
   1   -1    1   -1    ## -i+N-1 >= 0
   1    0    1   -1    ## N-1 >= 0
*)


Definition sample_domain3 := [
    (** N | i | const *)
    (** 1. -i <= 0 (i >= 0) *)
    ([0; -1], 0);
    (** 2. i-N<=-1 (i<=N-1) *)
    ([-1; 1], -1);
    (** 3. N - 1 >= 0 (-N <= -1)*)
    ([-1; 0], -1)
].


(*
# ----------------------------------------------  3.2 Scattering
SCATTERING
3 7 3 1 0 1
# e/i| c1   c2   c3 |  i |  N |  1  
   0   -1    0    0    0    0    2    ## c1 == 2
   0    0   -1    0    1    0    0    ## c2 == i
   0    0    0   -1    0    0    0    ## c3 == 0
*)

(** (0, i, 0) *)
Definition sample_sctt3: AffineFunction := [
    ([ 0; 0], 2);
    ([ 0; 1], 0);
    ([ 0; 0], 0)
].


(* 
# ----------------------------------------------  2.3 Access
WRITE
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   10    ## Arr == x
   0    0   -1    1    0    0    0    ## [1] == i
*)

Definition sample_waccess3: list AccessFunction := (
    (** x[i] *)
    10%positive,
    [
        (** N | i *)
        ([0; 1], 0)
    ]
)::nil.

(*
READ
2 6 2 1 0 1
# e/i| Arr  [1]|  i |  N |  1  
   0   -1    0    0    0   10    ## Arr == x
   0    0   -1    1    0    0    ## [1] == i

READ
2 6 2 1 0 1
# e/i| Arr  [1]|  i |  N |  1  
   0   -1    0    0    0   13    ## Arr == z
   0    0   -1    1    0    0    ## [1] == i
*)

Definition sample_raccess3: list AccessFunction := [
    (
        (** x[i] *)
        10%positive, 
        [
            (** N | i *)
            ([0; 1], 0)
        ]
    );
    (
        (** z[i] *)
        13%positive, 
        [
            (** N | i *)
            ([0; 1], 0)
        ]
    )
].

(* transformation is set as identity *)
Definition sample_transformation3 := [
    ([1; 0], 0);
    ([0; 1], 0)
].


(*
<arrays>
# Number of arrays
15
# Mapping array-identifiers/array-names
2 N (0)
1 i (1)
3 j (2)
4 B, 5 A, 6 u1
7 v1, 8 u2   , 9 v2
10 x, 11 beta, 12 y
13 z, 14 w,    15 alpha
</arrays>
*)

(* x[i] = x[i] + z[i]; ; *)
Definition sample_cinstr3 := 
    CPolIRs.Instr.Iassign 
        (* x[i] *)
        (CPolIRs.Instr.Aarr 
            10%positive  
              (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat))
            CTy.int32s
        )
        (CPolIRs.Instr.Ebinop
            Cop.Oadd
                (* x[i] *)
                (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 10%positive  
                  (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat)) CTy.int32s ) CTy.int32s)
                (* z[i] *)
                (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 13%positive  
                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat)) CTy.int32s ) CTy.int32s)
            CTy.int32s
        )
.

(* Instruction 4: w[i] = w[i] + alpha* B[i][j]*x[j]; *)
(* Domain: 
# ----------------------------------------------  4.1 Domain
DOMAIN
5 5 2 0 0 1
# e/i|  i    j |  N |  1  
   1    1    0    0    0    ## i >= 0
   1   -1    0    1   -1    ## -i+N-1 >= 0
   1    0    0    1   -1    ## N-1 >= 0
   1    0    1    0    0    ## j >= 0
   1    0   -1    1   -1    ## -j+N-1 >= 0
*)
Definition sample_domain4: Domain := [
    (** N | i j | const *)
    (** 1. -i <= 0 (i >= 0) *)
    ([0; -1; 0], 0);
    (** 2. i-N<=-1 (i<=N-1) *)
    ([-1; 1; 0], -1);
    (** 3. N - 1 >= 0 (-N <= -1)*)
    ([-1; 0; 0], -1);
    (** 4. j >= 0 (-j <= 0) *)
    ([0; 0; -1], 0);
    (** 5. j <= N - 1 (-j+N-1 >= 0) *)
    ([-1; 0; 1], -1)
].

(*
# ----------------------------------------------  4.2 Scattering
SCATTERING
5 10 5 2 0 1
# e/i| c1   c2   c3   c4   c5 |  i    j |  N |  1  
   0   -1    0    0    0    0    0    0    0    3    ## c1 == 3
   0    0   -1    0    0    0    1    0    0    0    ## c2 == i
   0    0    0   -1    0    0    0    0    0    0    ## c3 == 0
   0    0    0    0   -1    0    0    1    0    0    ## c4 == j
   0    0    0    0    0   -1    0    0    0    0    ## c5 == 0
*)

(** (0, i, 0, j, 0) *)
Definition sample_sctt4: AffineFunction := [
    ([ 0; 0; 0], 3);
    ([ 0; 1; 0], 0);
    ([ 0; 0; 0], 0);
    ([ 0; 0; 1], 0);
    ([ 0; 0; 0], 0)
].

(* 
# ----------------------------------------------  4.3 Access
WRITE
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   14    ## Arr == w
   0    0   -1    1    0    0    0    ## [1] == i
*)

Definition sample_waccess4: list AccessFunction := (
    (** w[i] *)
    14%positive, 
    [
        (** N | i j *)
        ([0; 1; 0], 0)
    ]
)::nil.

(*
READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   14    ## Arr == w
   0    0   -1    1    0    0    0    ## [1] == i

READ
1 6 1 2 0 1
# e/i| Arr|  i    j |  N |  1  
   0   -1    0    0    0   15    ## Arr == alpha

READ
3 8 3 2 0 1
# e/i| Arr  [1]  [2]|  i    j |  N |  1  
   0   -1    0    0    0    0    0    4    ## Arr == B
   0    0   -1    0    1    0    0    0    ## [1] == i
   0    0    0   -1    0    1    0    0    ## [2] == j

READ
2 7 2 2 0 1
# e/i| Arr  [1]|  i    j |  N |  1  
   0   -1    0    0    0    0   10    ## Arr == x
   0    0   -1    0    1    0    0    ## [1] == j
*)

Definition sample_raccess4: list AccessFunction := [
    (
        (** w[i] *)
        14%positive,
        [
            (** N | i j *)
            ([0; 1; 0], 0)
        ]
    );
    (
        (** alpha *)
        15%positive, 
        [
            (** N | i j *)
        ]
    );
    (
        (** B[i][j] *)
        4%positive, 
        [
            (** N | i j *)
            ([0; 1; 0], 0);
            ([0; 0; 1], 0)
        ]
    );
    (
        (** x[j] *)
        10%positive, 
        [
            (** N | i j *)
            ([0; 0; 1], 0)
        ]
    )
].

(* transformation is set as identity *)
Definition sample_transformation4 := [
    ([1; 0; 0], 0);
    ([0; 1; 0], 0);
    ([0; 0; 1], 0)
].

(*
<arrays>
# Number of arrays
15
# Mapping array-identifiers/array-names
2 N (0)
1 i (1)
3 j (2)
4 B, 5 A, 6 u1
7 v1, 8 u2   , 9 v2
10 x, 11 beta, 12 y
13 z, 14 w,    15 alpha
</arrays>
*)

(* x[i] = x[i] + beta* B[j][i]*y[j]; *)
(* w[i] = w[i] + alpha* B[i][j]*x[j]; *)
Definition sample_cinstr4 := 
    CPolIRs.Instr.Iassign 
        (* w[i] *)
        (CPolIRs.Instr.Aarr 
            14%positive  
              (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat))
            CTy.int32s
        )
        (CPolIRs.Instr.Ebinop
            Cop.Oadd
                (* w[i] *)
                (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 14%positive  
                  (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 1%nat)) CTy.int32s ) CTy.int32s)
                (* alpha* B[i][j]*x[j] *)
                (CPolIRs.Instr.Ebinop Cop.Omul
                    (* alpha *)
                      (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Avar 15%positive CTy.int32s)
                        CTy.int32s) 
                    (* B[j][i]*y[j]*)
                    (CPolIRs.Instr.Ebinop Cop.Omul
                    (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 4%positive 
                      (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 1%nat)
                        (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)))
                        CTy.int32s) CTy.int32s)
                      (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 10%positive  
                        (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 2%nat)) CTy.int32s ) CTy.int32s) CTy.int32s)
                    CTy.int32s                    
                  )
            CTy.int32s
        )
.

(*
<arrays>
# Number of arrays
15
# Mapping array-identifiers/array-names
1 i
2 N
3 j
4 B
5 A
6 u1
7 v1
8 u2
9 v2
10 x
11 beta
12 y
13 z
14 w
15 alpha
</arrays>
*)

Definition sample_pi1 := {|
    CPolIRs.PolyLang.pi_depth := 2%nat;
    CPolIRs.PolyLang.pi_instr := sample_cinstr1; 
    CPolIRs.PolyLang.pi_poly := sample_domain1;
    CPolIRs.PolyLang.pi_transformation := sample_transformation1;
    CPolIRs.PolyLang.pi_schedule := sample_sctt1;
    CPolIRs.PolyLang.pi_waccess := sample_waccess1;
    CPolIRs.PolyLang.pi_raccess := sample_raccess1;
|}.

Definition sample_pi2 := {|
    CPolIRs.PolyLang.pi_depth := 2%nat;
    CPolIRs.PolyLang.pi_instr := sample_cinstr2;
    CPolIRs.PolyLang.pi_poly := sample_domain2;
    CPolIRs.PolyLang.pi_transformation := sample_transformation2;
    CPolIRs.PolyLang.pi_schedule := sample_sctt2;
    CPolIRs.PolyLang.pi_waccess := sample_waccess2;
    CPolIRs.PolyLang.pi_raccess := sample_raccess2;
|}.

Definition sample_pi3 := {|
    CPolIRs.PolyLang.pi_depth := 1%nat;
    CPolIRs.PolyLang.pi_instr := sample_cinstr3; 
    CPolIRs.PolyLang.pi_poly := sample_domain3;
    CPolIRs.PolyLang.pi_transformation := sample_transformation3;
    CPolIRs.PolyLang.pi_schedule := sample_sctt3;
    CPolIRs.PolyLang.pi_waccess := sample_waccess3;
    CPolIRs.PolyLang.pi_raccess := sample_raccess3;
|}.

Definition sample_pi4 := {|
    CPolIRs.PolyLang.pi_depth := 2%nat;
    CPolIRs.PolyLang.pi_instr := sample_cinstr4; 
    CPolIRs.PolyLang.pi_poly := sample_domain4;
    CPolIRs.PolyLang.pi_transformation := sample_transformation4;
    CPolIRs.PolyLang.pi_schedule := sample_sctt4;
    CPolIRs.PolyLang.pi_waccess := sample_waccess4;
    CPolIRs.PolyLang.pi_raccess := sample_raccess4;
|}.

Definition sample_pis := 
    [sample_pi1; sample_pi2; sample_pi3; sample_pi4] 
.

Definition sample_varctxt := 
    [2%positive].

(**
1 i, 2 M, 3 j, 4 N
5 k, 6 K, 7 C, 8 beta
9 alpha, 10 A, 11 B
*)
Definition sample_vars := 
    [
    (1%positive, CTy.arr_type_intro CTy.int32s []); 
    (2%positive, CTy.arr_type_intro CTy.int32s []); 
    (3%positive, CTy.arr_type_intro CTy.int32s []); 
    (4%positive, CTy.arr_type_intro CTy.int32s [100;100]); 
    (5%positive, CTy.arr_type_intro CTy.int32s [100;100]); 
    (6%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (7%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (8%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (9%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (10%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (11%positive, CTy.arr_type_intro CTy.int32s []); 
    (12%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (13%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (14%positive, CTy.arr_type_intro CTy.int32s [100]); 
    (15%positive, CTy.arr_type_intro CTy.int32s [])].

Definition sample_cpol := (
  sample_pis, 
  sample_varctxt,
  sample_vars
).



Example raccesses_ok:
    opt_access_subset (CPolIRs.Instr.raccess sample_cinstr1) (Some sample_raccess1) = true /\
    opt_access_subset (CPolIRs.Instr.raccess sample_cinstr2) (Some sample_raccess2) = true /\
    opt_access_subset (CPolIRs.Instr.raccess sample_cinstr3) (Some sample_raccess3) = true /\
    opt_access_subset (CPolIRs.Instr.raccess sample_cinstr4) (Some sample_raccess4) = true.
Proof. simpl. firstorder. Qed.

Example waccesses_ok:
    opt_access_subset (CPolIRs.Instr.waccess sample_cinstr1) (Some sample_waccess1) = true /\
    opt_access_subset (CPolIRs.Instr.waccess sample_cinstr2) (Some sample_waccess2) = true /\
    opt_access_subset (CPolIRs.Instr.waccess sample_cinstr3) (Some sample_waccess3) = true /\
    opt_access_subset (CPolIRs.Instr.waccess sample_cinstr4) (Some sample_waccess4) = true.
Proof. simpl. firstorder. Qed.
