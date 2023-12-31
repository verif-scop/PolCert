(* 
Sample1: matmul.c
-- M, N, K: symbolic constants 
#pragma scop 
  for (i = 0; i < M; i++)     // i:depth 0 iterator of loop nests
    for (j = 0; j < N; j++)   // j:depth 1 iterator of loop nests
      for (k = 0; k < K; k++) // k:depth 2 iterator of loop nests
        C[i][j] = beta * C[i][j] + alpha * A[i][k] * B[k][j];
#pragma endscop 
Pluto scheduler will flip i/k loop.
for (k = 0; k < K; i++)
  for (j = 0; j < N; j++)
    for (i = 0; i < M; k++)
    C[i][j] = beta * C[i][j] + alpha * A[i][k] * B[k][j];
And the validator produce "true" bidirectionally, which means two loop nests are equivalent.
*)


(* Its openscop file generated by pluto before scheduling: *)
(*
# [File generated by the OpenScop Library 0.9.2]

<OpenScop>

# =============================================== Global
# Language
C

# Context
CONTEXT
0 5 0 0 0 3

# Parameters are provided
1
<strings>
M N K
</strings>
*)
(*
# Number of statements
1

# =============================================== Statement 1
# Number of relations describing the statement:
8

# ----------------------------------------------  1.1 Domain
DOMAIN
9 8 3 0 0 3
# e/i|  i    j    k |  M    N    K |  1  
   1    1    0    0    0    0    0    0    ## i >= 0
   1   -1    0    0    1    0    0   -1    ## -i+M-1 >= 0
   1    0    0    0    1    0    0   -1    ## M-1 >= 0
   1    0    1    0    0    0    0    0    ## j >= 0
   1    0   -1    0    0    1    0   -1    ## -j+N-1 >= 0
   1    0    0    0    0    1    0   -1    ## N-1 >= 0
   1    0    0    1    0    0    0    0    ## k >= 0
   1    0    0   -1    0    0    1   -1    ## -k+K-1 >= 0
   1    0    0    0    0    0    1   -1    ## K-1 >= 0
*)
Require Import PolyBase.
Require Import List.
Import List.ListNotations.
Require Import ZArith.
Require Import CPolIRs.
Require Import CTy.
Open Scope Z_scope.
Definition sample_domain: Domain := [
    (** M N K | i j k | const *)
    (** 1. -i <= 0 (i >= 0) *)
    ([0; 0; 0; -1; 0; 0], 0);
    (** 2. - M + i <= -1 (i <= M-1) *)
    ([-1; 0; 0; 1; 0; 0], -1);
    (** 3. M - 1 >= 0 (-M <= -1)*)
    ([-1; 0; 0; 0; 0; 0], -1);
    (** 4. j >= 0 (-j <= 0) *)
    ([0; 0; 0; 0; -1; 0], 0);
    (** 5. j <= N - 1 (-j+N-1 >= 0) *)
    ([0; -1; 0; 0; 1; 0], -1);
    (** 6. -N <= -1 (N - 1 >= 0) *)
    ([0; -1; 0; 0; 0; 0], -1);
    (** 7. -k <= 0*)
    ([0; 0; 0; 0; 0; -1], 0);
    (** 8. k <= K - 1 *)
    ([0; 0; -1; 0; 0; 1], -1);
    (** 9. -K <= -1*)
    ([0; 0; -1; 0; 0; 0], -1)
].

(*
# ----------------------------------------------  1.2 Scattering
SCATTERING
7 15 7 3 0 3
# e/i| c1   c2   c3   c4   c5   c6   c7 |  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    0    0    0    0    0    0    0    ## c1 == 0
   0    0   -1    0    0    0    0    0    1    0    0    0    0    0    0    ## c2 == i
   0    0    0   -1    0    0    0    0    0    0    0    0    0    0    0    ## c3 == 0
   0    0    0    0   -1    0    0    0    0    1    0    0    0    0    0    ## c4 == j
   0    0    0    0    0   -1    0    0    0    0    0    0    0    0    0    ## c5 == 0
   0    0    0    0    0    0   -1    0    0    0    1    0    0    0    0    ## c6 == k
   0    0    0    0    0    0    0   -1    0    0    0    0    0    0    0    ## c7 == 0
*)

(** (0, i, 0, j, 0, k, 0) *)
(* Definition sample_sctt: AffineFunction := [
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 1; 0; 0], 0);
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 0; 1; 0], 0);
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 0; 0; 1], 0);
    ([ 0; 0; 0; 0; 0; 0], 0)
]. *)

Definition sample_sctt: AffineFunction := [
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 1; 0; 0], 0);
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 0; 1; 0], 0);
    ([ 0; 0; 0; 0; 0; 0], 0);
    ([ 0; 0; 0; 0; 0; 1], 0);
    ([ 0; 0; 0; 0; 0; 0], 0)
].

(* 
# ----------------------------------------------  1.3 Access
WRITE
3 11 3 3 0 3
# e/i| Arr  [1]  [2]|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    0    0    7    ## Arr == C
   0    0   -1    0    1    0    0    0    0    0    0    ## [1] == i
   0    0    0   -1    0    1    0    0    0    0    0    ## [2] == j
*)

Definition sample_waccess: list AccessFunction := (
    (** C[i][j] *)
    7%positive, 
    [
        (** M N K | i j k *)
        ([0; 0; 0; 1; 0; 0], 0);
        ([0; 0; 0; 0; 1; 0], 0)
    ]
)::nil.

(*
READ
1 9 1 3 0 3
# e/i| Arr|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    8    ## Arr == beta

READ
3 11 3 3 0 3
# e/i| Arr  [1]  [2]|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    0    0    7    ## Arr == C
   0    0   -1    0    1    0    0    0    0    0    0    ## [1] == i
   0    0    0   -1    0    1    0    0    0    0    0    ## [2] == j

READ
1 9 1 3 0 3
# e/i| Arr|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    9    ## Arr == alpha

READ
3 11 3 3 0 3
# e/i| Arr  [1]  [2]|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    0    0   10    ## Arr == A
   0    0   -1    0    1    0    0    0    0    0    0    ## [1] == i
   0    0    0   -1    0    0    1    0    0    0    0    ## [2] == k

READ
3 11 3 3 0 3
# e/i| Arr  [1]  [2]|  i    j    k |  M    N    K |  1  
   0   -1    0    0    0    0    0    0    0    0   11    ## Arr == B
   0    0   -1    0    0    0    1    0    0    0    0    ## [1] == k
   0    0    0   -1    0    1    0    0    0    0    0    ## [2] == j
*)

Definition sample_raccess: list AccessFunction := [
    (
        (** beta *)
        8%positive, 
        [
            (** M N K | i j k *)
        ]
    );
    (
        (** C[i][j] *)
        7%positive, 
        [
            (** M N K | i j k *)
            ([0; 0; 0; 1; 0; 0], 0);
            ([0; 0; 0; 0; 1; 0], 0)
        ]
    );
    (
        (** alpha *)
        9%positive, 
        [
            (** M N K | i j k *)
        ]
    );
    (
        (** A[i][k] *)
        10%positive, 
        [
            (** M N K | i j k *)
            ([0; 0; 0; 1; 0; 0], 0);
            ([0; 0; 0; 0; 0; 1], 0)
        ]
    );
    (
        (** B[k][j] *)
        11%positive, 
        [
            (** M N K | i j k *)
            ([0; 0; 0; 0; 0; 1], 0);
            ([0; 0; 0; 0; 1; 0], 0)
        ]
    )
].

(* transformation is set as identity *)
Definition sample_transformation := [
    ([1; 0; 0; 0; 0; 0], 0);
    ([0; 1; 0; 0; 0; 0], 0);
    ([0; 0; 1; 0; 0; 0], 0);
    ([0; 0; 0; 1; 0; 0], 0);
    ([0; 0; 0; 0; 1; 0], 0);
    ([0; 0; 0; 0; 0; 1], 0)
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

(* M(2) N(4) K(6) i(1) j(3) k(5), they are nat 0-5 in CInstr.varz*)
Definition sample_cinstr := 
    CPolIRs.Instr.Iassign 
        (* C[i][j] *)
        (CPolIRs.Instr.Aarr 
            7%positive 
            (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 3%nat) 
                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 4%nat )))
            CTy.int32s
        )
        (CPolIRs.Instr.Ebinop
            Cop.Oadd
                (* beta * C[i][j] *)
                (CPolIRs.Instr.Ebinop
                    Cop.Omul 
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Avar 8%positive CTy.int32s) CTy.int32s)
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 
                            7%positive 
                            (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 3%nat) 
                                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 4%nat)))
                                CTy.int32s
                        ) CTy.int32s)
                        CTy.int32s
                )
                (* alpha * A[i][k] * B[k][j] *)
                (CPolIRs.Instr.Ebinop Cop.Omul 
                    (* alpha *)
                    (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Avar 9%positive CTy.int32s) CTy.int32s)
                    (* A[i][k] * B[k][j] *)
                    (CPolIRs.Instr.Ebinop Cop.Omul
                        (* A[i][k] *)
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 10%positive 
                            (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 3%nat) 
                                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 5%nat)))
                                CTy.int32s) CTy.int32s)
                        (CPolIRs.Instr.Eaccess (CPolIRs.Instr.Aarr 11%positive 
                            (CPolIRs.Instr.MAcons (CPolIRs.Instr.MAvarz 5%nat) 
                                (CPolIRs.Instr.MAsingleton (CPolIRs.Instr.MAvarz 4%nat)))
                                CTy.int32s) CTy.int32s)
                            CTy.int32s
                    )
                    CTy.int32s                    
                )
                CTy.int32s
        )
.


Example waccess_ok:
    opt_access_subset (CPolIRs.Instr.waccess sample_cinstr) (Some sample_waccess) = true.
Proof.
    simpl. reflexivity.
Qed.

Example raccesses_ok:
    opt_access_subset (CPolIRs.Instr.raccess sample_cinstr) (Some sample_raccess) = true.
Proof. simpl. reflexivity. Qed.
    
Definition sample_pi := {|
    CPolIRs.PolyLang.pi_depth := 3%nat;
    CPolIRs.PolyLang.pi_instr := sample_cinstr; 
    CPolIRs.PolyLang.pi_poly := sample_domain;
    CPolIRs.PolyLang.pi_transformation := sample_transformation;
    CPolIRs.PolyLang.pi_schedule := sample_sctt;
    CPolIRs.PolyLang.pi_waccess := sample_waccess;
    CPolIRs.PolyLang.pi_raccess := sample_raccess;
|}.

Definition sample_pis := 
    [sample_pi] 
.

Definition sample_varctxt := 
    [2%positive; 4%positive; 6%positive].

(**
1 i, 2 M, 3 j, 4 N
5 k, 6 K, 7 C, 8 beta
9 alpha, 10 A, 11 B
*)
(**
Note that, in our model, iterators are nameless.
so i j k here is redundant.
And in fact, 
*)
Definition sample_vars := 
    [(1%positive, CTy.arr_type_intro CTy.int32s []); 
    (2%positive, CTy.arr_type_intro CTy.int32s []); 
    (3%positive, CTy.arr_type_intro CTy.int32s []); 
    (4%positive, CTy.arr_type_intro CTy.int32s []); 
    (5%positive, CTy.arr_type_intro CTy.int32s []); 
    (6%positive, CTy.arr_type_intro CTy.int32s []); 
    (7%positive, CTy.arr_type_intro CTy.int32s [100;100]); 
    (8%positive, CTy.arr_type_intro CTy.int32s []); 
    (9%positive, CTy.arr_type_intro CTy.int32s []); 
    (10%positive, CTy.arr_type_intro CTy.int32s [100;100]); 
    (11%positive, CTy.arr_type_intro CTy.int32s [100;100])].

Definition sample_cpol := (
  sample_pis, 
  sample_varctxt,
  sample_vars
).
(*
# ----------------------------------------------  1.4 Statement Extensions
# Number of Statement Extensions
1


# =============================================== Extensions
<scatnames>
b0 i b1 j b2 k b3
</scatnames>

<arrays>
# Number of arrays
11
# Mapping array-identifiers/array-names
1 i
2 M
3 j
4 N
5 k
6 K
7 C
8 beta
9 alpha
10 A
11 B
</arrays>

<coordinates>
# File name
(null)
# Starting line and column
73 0
# Ending line and column
77 0
# Indentation
2
</coordinates>

</OpenScop>
*)
