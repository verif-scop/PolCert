Require Import ZArith.
Require Import Result.
Require Import ImpureAlarmConfig.
Require Import String.

Require Import PolIRs.

Require Import AST.
Require Import Base.
Require Import PolyBase.
Require Import List.
Import ListNotations.

Require Import Linalg.

Module Extractor (PolIRs: POLIRS).

(* Note: empty domain contains exactly one instance: [] (empty list) *)

(** generate aff from the deepest *)
(** cur_dim, from 0 to depth *)
Fixpoint expr_to_aff (e: PolIRs.Loop.expr): result (list Z * Z) := 
    match e with 
    (* base case, c*)
    | PolIRs.Loop.Constant z => Okk (nil, z)
    (* base case, xni + c / xni *)
    | PolIRs.Loop.Var n => Okk (V0 n ++ [1%Z] , 0%Z)
    (* base case, anixni + c / anixni*)
    | PolIRs.Loop.Mult z e2 => 
        match expr_to_aff e2 with
        | Okk (aff2, c2) => 
                Okk (mult_vector z aff2, z * c2)
        | Err msg => Err "Expr to aff failed, mult."%string
        end
    (* recursive case *)
    | PolIRs.Loop.Sum e1 e2 =>
        match expr_to_aff e1, expr_to_aff e2 with
        | Okk (aff1, c1), Okk (aff2, c2) => 
            Okk (add_vector aff1 aff2, c1 + c2)
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end
    | _ => Err "Expr to aff failed."%string
    end.

Example test_expr_to_aff_1: 
    expr_to_aff (PolIRs.Loop.Constant 5%Z) = Okk ([], 5%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_2:
    (expr_to_aff (PolIRs.Loop.Var 3)) = Okk ([0%Z; 0%Z; 0%Z; 1%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_3:
    (expr_to_aff (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))) = Okk ([0%Z; 0%Z; 0%Z; 0%Z; 2%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_4: 
    (expr_to_aff (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z))) = Okk ([0%Z; 0%Z; 0%Z; 1%Z], 5%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_5: 
    (expr_to_aff (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Var 3) 
                        (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))
                    )) 
    = Okk ([0%Z; 0%Z; 0%Z; 1%Z; 2%Z], 0%Z).
Proof. reflexivity. Qed.

Example test_expr_to_aff_6: 
    (expr_to_aff (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Var 3) 
                    (PolIRs.Loop.Sum 
                        (PolIRs.Loop.Mult 2%Z (PolIRs.Loop.Var 4))
                        (PolIRs.Loop.Constant 5%Z)
                    )))
    = Okk ([0%Z; 0%Z; 0%Z; 1%Z; 2%Z], 5%Z).
Proof. reflexivity. Qed.

Fixpoint exprlist_to_aff (es: list PolIRs.Loop.expr) (depth: nat): result (list (list Z * Z)) 
:= 
    match es with 
    | [] => Okk []
    | e :: es' => 
        match (expr_to_aff e) with 
        | Okk aff => 
            match (exprlist_to_aff es' depth) with 
            | Okk affs => Okk (aff :: affs)
            | Err msg => Err msg
            end
        | Err msg => Err msg
        end
    end.

Definition make_le_constr (aff1 aff2: list Z * Z): list Z * Z := 
    let (aff1, c1) := aff1 in 
    let (aff2, c2) := aff2 in 
    (add_vector aff1 (map Z.opp aff2), c2 - c1).

Example test_make_le_constr_1:
    make_le_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 10%Z) 
    = ([-1%Z; 0%Z; -1%Z], 0%Z).
Proof. reflexivity. Qed.
 
Example test_make_le_constr_2:
    make_le_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 20%Z) 
    = ([-1%Z; 0%Z; -1%Z], 10%Z).
Proof. reflexivity. Qed.

Definition make_ge_constr (aff1 aff2: list Z * Z): list Z * Z := 
    let (aff1, c1) := aff1 in 
    let (aff2, c2) := aff2 in 
    (add_vector (map Z.opp aff1) aff2, c1 - c2).

Example test_make_ge_constr:
    make_ge_constr ([1%Z; -1%Z], 10%Z) ([2%Z; -1%Z; 1%Z], 10%Z) 
    = ([1%Z; 0%Z; 1%Z], 0%Z).
Proof. reflexivity. Qed.


(** test to constraint *)
Fixpoint test_to_aff (tst: PolIRs.Loop.test): result (list (list Z * Z)) := 
    match tst with 
    | PolIRs.Loop.LE e1 e2 => 
        match (expr_to_aff e1), (expr_to_aff e2) with 
        | Okk aff1, Okk aff2 => 
            Okk [make_le_constr aff1 aff2]
        | _, _ => Err "Test to aff failed"%string
        end
    | PolIRs.Loop.EQ e1 e2 => 
        match (expr_to_aff e1), (expr_to_aff e2) with 
        | Okk aff1, Okk aff2 => 
            Okk [make_le_constr aff1 aff2; make_ge_constr aff1 aff2]
        | _, _ => Err "Test to aff failed"%string
        end
    | PolIRs.Loop.And tst1 tst2 => 
        match (test_to_aff tst1), (test_to_aff tst2) with 
        | Okk aff1, Okk aff2 => 
            Okk (aff1 ++ aff2)
        | _, _ => Err "Test to aff failed"%string
        end
    | _ => Err "Test to aff failed"%string
    end.

(** depth is the loop's depth (counting ctxt), from zero *)
Definition lb_to_constr (lb: PolIRs.Loop.expr) (depth: nat): result (list Z * Z) := 
    match (expr_to_aff lb) with 
    | Okk (aff, c) => Okk ((resize depth aff) ++ [-1%Z], Z.opp c) 
    | Err msg => Err msg
    end
.

(** $3 + 5 <= $4  ==> $3 - $4 <= -5 *)
Example test_lb_to_constr_1:
    lb_to_constr (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z)) 4
    = Okk ([0%Z; 0%Z; 0%Z; 1%Z; -1%Z], -5%Z).
Proof. reflexivity. Qed.

Definition ub_to_constr (ub: PolIRs.Loop.expr) (depth: nat): result (list Z * Z) := 
    match (expr_to_aff ub) with
    | Okk (aff, c) => Okk ((resize depth (map Z.opp aff)) ++ [1%Z], c-1)    (** < => <= -1*)
    | Err msg => Err msg 
    end
.

(** $3 + 5 > $4 => -$3 + $4 < 5 *)
Example test_ub_to_constr_1:
    ub_to_constr (PolIRs.Loop.Sum (PolIRs.Loop.Var 3) (PolIRs.Loop.Constant 5%Z)) 4
    = Okk ([0%Z; 0%Z; 0%Z; -1%Z; 1%Z], 4%Z).
Proof. reflexivity. Qed.

(** $3 + 5 >= $4 => -$3 + $4 <= 5 *)


(** depth is nested loop's depth, not counting seq/nested seq; pos record the relative seq *)
(** final schedule is not exactly 2n+1, due to nests seq exists *)
(** depth equals to context length + iterator count *)

Fixpoint extract_stmt (stmt: PolIRs.Loop.stmt) (constrs: Domain) (depth: nat) (sched_prefix: Schedule) {struct stmt}: result (list PolIRs.PolyLang.PolyInstr) := 
    (** normal seq schedule dimension *)
    match stmt with 
    | PolIRs.Loop.Instr instr es => 
        match (exprlist_to_aff es depth) with 
        | Okk tf => 
            (* let sched_prefix' := sched_prefix ++ [(nil, Z.of_nat pos)] in  *)
            match PolIRs.Instr.waccess instr, PolIRs.Instr.raccess instr with 
            | Some w, Some r => 
                Okk [{|
                    PolIRs.PolyLang.pi_depth := pred depth; 
                    (* map (fun x => Pos.of_nat x) (seq 1 (pred depth)); *)
                    PolIRs.PolyLang.pi_instr := instr;
                    (** inherit constraints as domain *)
                    PolIRs.PolyLang.pi_poly := constrs; 
                    (** inherit prefix timestamp's calculation *)
                    PolIRs.PolyLang.pi_schedule := sched_prefix;  
                    PolIRs.PolyLang.pi_transformation := tf;
                    PolIRs.PolyLang.pi_waccess := w;
                    PolIRs.PolyLang.pi_raccess := r;                
                |}]
            | _, _ => 
                Err "Instr extract failed"%string
            end
        | Err msg => Err msg
        end
    | PolIRs.Loop.Seq stmts => 
        (* let sched_prefix' := sched_prefix ++ [(nil, Z.of_nat pos)] in  *)
            extract_stmts stmts constrs depth sched_prefix 0
    | PolIRs.Loop.Loop lb ub stmt => 
        let lb_constr := (lb_to_constr lb depth) in 
        let ub_constr := (ub_to_constr ub depth) in 
        match lb_constr, ub_constr with
        | Okk lb_constr', Okk ub_constr' => 
            let constrs' := constrs ++ [lb_constr'; ub_constr'] in 
            (** add schedule dimension for the loop *)
            let sched_prefix' := sched_prefix ++ [(repeat 0%Z depth ++ [1%Z], 0%Z)] in
            extract_stmt stmt constrs' (S depth) sched_prefix'
        | _, _ => Err "Loop bound to aff failed"%string
        end
    | PolIRs.Loop.Guard test stmt => 
        let test_constrs := (test_to_aff test) in
        match test_constrs with
        | Okk test_constrs' => 
            let constrs' := constrs ++ test_constrs' in 
            extract_stmt stmt constrs' depth sched_prefix
        | Err msg => Err msg 
        end 
    end
with extract_stmts (stmts: PolIRs.Loop.stmt_list) (constrs: Domain) (depth: nat) (sched_prefix: Schedule) (pos: nat) {struct stmts}: result (list PolIRs.PolyLang.PolyInstr) := 
    match stmts with 
    | PolIRs.Loop.SNil => Okk nil 
    | PolIRs.Loop.SCons stmt stmts' => 
        let sched_prefix' := sched_prefix ++ [(nil, Z.of_nat pos)] in
        match extract_stmt stmt constrs depth sched_prefix' with 
        | Okk pis => 
            match extract_stmts stmts' constrs depth sched_prefix (S pos) with 
            | Okk pis' => Okk (pis ++ pis')
            | Err msg => Err msg
            end
        | Err msg => Err msg
        end
    end.


Example test_extract_1: 
    extract_stmt 
    (PolIRs.Loop.Loop 
        (PolIRs.Loop.Constant 0%Z) 
        (PolIRs.Loop.Constant 10%Z) 
        (PolIRs.Loop.Instr (PolIRs.Instr.dummy_instr) [PolIRs.Loop.Var 1])
    ) [] 1 [] = 
    match PolIRs.Instr.waccess PolIRs.Instr.dummy_instr, PolIRs.Instr.raccess PolIRs.Instr.dummy_instr with 
    | Some w, Some r =>
    Okk
    [{|
        PolIRs.PolyLang.pi_depth := 1;
        PolIRs.PolyLang.pi_instr := PolIRs.Instr.dummy_instr;
        PolIRs.PolyLang.pi_poly := [([0; -1], 0); ([0; 1], 9)];
        PolIRs.PolyLang.pi_schedule := [([0; 1], 0)];
        PolIRs.PolyLang.pi_transformation := [([0; 1], 0)];
        PolIRs.PolyLang.pi_waccess := w;
        PolIRs.PolyLang.pi_raccess := r
    |}]
    | _, _ => Err "Instr extract failed"%string
    end
    .
Proof. simpl. reflexivity. Qed.

Example test_extract_2: 
    extract_stmt 
    (PolIRs.Loop.Loop 
        (PolIRs.Loop.Constant 0%Z) 
        (PolIRs.Loop.Var 0) 
        (PolIRs.Loop.Instr (PolIRs.Instr.dummy_instr) [PolIRs.Loop.Var 1])
    ) [] 1 [] = 
    match PolIRs.Instr.waccess PolIRs.Instr.dummy_instr, PolIRs.Instr.raccess PolIRs.Instr.dummy_instr with 
    | Some w, Some r =>
    Okk
    [{|
        PolIRs.PolyLang.pi_depth := 1;
        PolIRs.PolyLang.pi_instr := PolIRs.Instr.dummy_instr;
        PolIRs.PolyLang.pi_poly := [([0; -1], 0); ([-1; 1], -1)];
        PolIRs.PolyLang.pi_schedule := [([0; 1], 0)];
        PolIRs.PolyLang.pi_transformation := [([0; 1], 0)];
        PolIRs.PolyLang.pi_waccess := w;
        PolIRs.PolyLang.pi_raccess := r
    |}]
    | _, _ => Err "Instr extract failed"%string
    end.
Proof. simpl. reflexivity. Qed.

Example test_extract_3: 
    extract_stmt 
    (PolIRs.Loop.Loop 
        (PolIRs.Loop.Constant 0%Z) 
        (PolIRs.Loop.Var 0) 
        (PolIRs.Loop.Loop
            (PolIRs.Loop.Constant 0%Z) 
            (PolIRs.Loop.Var 1) 
            (PolIRs.Loop.Instr (PolIRs.Instr.dummy_instr) [PolIRs.Loop.Var 1; PolIRs.Loop.Var 2])
        )
    ) [] 1 [] = 
    match PolIRs.Instr.waccess PolIRs.Instr.dummy_instr, PolIRs.Instr.raccess PolIRs.Instr.dummy_instr with 
    | Some w, Some r =>
    Okk
    [{|
         PolIRs.PolyLang.pi_depth := 2;
       PolIRs.PolyLang.pi_instr := PolIRs.Instr.dummy_instr;
       PolIRs.PolyLang.pi_poly :=
         [([0; -1], 0); ([-1; 1], -1); ([0; 0; -1], 0); ([0; -1; 1], -1)];
       PolIRs.PolyLang.pi_schedule := [([0; 1], 0); ([0; 0; 1], 0)];
       PolIRs.PolyLang.pi_transformation := [([0; 1], 0); ([0; 0; 1], 0)];
       PolIRs.PolyLang.pi_waccess := w;
       PolIRs.PolyLang.pi_raccess := r
     |}]
     | _, _ => Err "Instr extract failed"%string
     end
     .
Proof. simpl. reflexivity. Qed.

(** 
    Loop $1, 0 => $0:
        I($1); 
        Loop $2, 0 => $1: 
            I($1, $2);
*)
Example test_extract_4: 
    extract_stmt 
    (PolIRs.Loop.Loop 
        (PolIRs.Loop.Constant 0%Z) 
        (PolIRs.Loop.Var 0) 
        (PolIRs.Loop.Seq 
            (PolIRs.Loop.SCons 
            (PolIRs.Loop.Instr (PolIRs.Instr.dummy_instr) [PolIRs.Loop.Var 1])
            (
            PolIRs.Loop.SCons
            (PolIRs.Loop.Loop
                (PolIRs.Loop.Constant 0%Z) 
                (PolIRs.Loop.Var 1)
                (PolIRs.Loop.Instr (PolIRs.Instr.dummy_instr) [PolIRs.Loop.Var 1; PolIRs.Loop.Var 2])
            )
            PolIRs.Loop.SNil
            ))
        )
    ) [] 1 [] = 
    match PolIRs.Instr.waccess PolIRs.Instr.dummy_instr, PolIRs.Instr.raccess PolIRs.Instr.dummy_instr with
    | Some w, Some r =>
    Okk
    [{|
        PolIRs.PolyLang.pi_depth := 1;
        PolIRs.PolyLang.pi_instr := PolIRs.Instr.dummy_instr;
       PolIRs.PolyLang.pi_poly := [([0; -1], 0); ([-1; 1], -1)];
       (* $0, $1 => $1, 0 *)
       PolIRs.PolyLang.pi_schedule := [([0; 1], 0); ([], 0)];  
       PolIRs.PolyLang.pi_transformation := [([0; 1], 0)];
       PolIRs.PolyLang.pi_waccess := w;
       PolIRs.PolyLang.pi_raccess := r
     |}
     ;
    {|
        PolIRs.PolyLang.pi_depth := 2;
        PolIRs.PolyLang.pi_instr := PolIRs.Instr.dummy_instr;
      PolIRs.PolyLang.pi_poly :=
        [([0; -1], 0); ([-1; 1], -1); ([0; 0; -1], 0); ([0; -1; 1], -1)];
      (* $0, $1, $2 => $1, 1, $2 *)
      PolIRs.PolyLang.pi_schedule := [([0; 1], 0); ([], 1); ([0; 0; 1], 0)];
      PolIRs.PolyLang.pi_transformation := [([0; 1], 0); ([0; 0; 1], 0)];
      PolIRs.PolyLang.pi_waccess := w;
      PolIRs.PolyLang.pi_raccess := r
    |}]
    | _, _ => Err "Instr extract failed"%string
     end
    .
Proof. simpl. 
        destruct (PolIRs.Instr.waccess PolIRs.Instr.dummy_instr) eqn: wacc;
        destruct (PolIRs.Instr.raccess PolIRs.Instr.dummy_instr) eqn: racc; eauto.
Qed.

Definition extractor (loop: PolIRs.Loop.t): result PolIRs.PolyLang.t :=
    let '(stmt, varctxt, vars) := loop in 
    let pol := extract_stmt stmt [] (length varctxt) [] in 
    match pol with
    | Okk pol => 
        Okk (pol, varctxt, vars)
    | Err msg => Err msg 
    end
.

End Extractor.
