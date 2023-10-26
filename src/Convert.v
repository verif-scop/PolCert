Require Import Bool.
Require Import Result.
Require Import Csyntax.
Require Import Cop. 
Require Import Ctypes.
Require Import String.
Require Import CPolIRs.
Require Import AST.
Require Import List. 
Require Import ZArith.
Require Import Integers.
Require Import PolyBase.
Require Import CInstr.
Require Import Maps.
Require Import Misc.
Import ListNotations.

(******************************************************)
(*********** Reconvert CLoop to Csyntax ***************)
(******************************************************)

(** Convert the scop (in CSyntax) to more concise syntax, CLoop. *)
(** The array indexing is resugared *)


(** 1. Csyntax instruction to cinstr *)
(** 1.1 affine expression to Cinstr may-affine expression *)

Fixpoint convert_aff_expr_cinstr_ma_expr (expr: Csyntax.expr) (ctxt: PTree.t nat): result CInstr.ma_expr := 
    match expr with 
    | Csyntax.Eval v ty => 
        match v with 
        | Values.Vint n => 
            Okk (CInstr.MAval (Int.signed n))
        | _ => Err "convert_aff_expr_cinstr should not contain Z"%string
        end
    | Csyntax.Evar id ty => 
        match ctxt!id with 
        | Some n => Okk (CInstr.MAvarz n)
        | _ => Err "convert_aff_expr_cinstr Evar failed"%string
        end
    | Csyntax.Eunop op r ty => 
        match convert_aff_expr_cinstr_ma_expr r ctxt with 
        | Okk r => Okk (CInstr.MAunop op r)
        | Err msg => Err msg
        end
    | Csyntax.Ebinop op r1 r2 ty => 
        match convert_aff_expr_cinstr_ma_expr r1 ctxt, convert_aff_expr_cinstr_ma_expr r2 ctxt with 
        | Okk r1, Okk r2 => Okk (CInstr.MAbinop op r1 r2)
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end
    | _ => Err "not supported may-affine expression (CInstr)"%string
    end .

Definition check_type_int32s ty := 
    match ty with 
    | Ctypes.Tint I32 Signed noattr => 
        match (Ctypes.attr_alignas noattr) with 
        | None => (Bool.eqb (Ctypes.attr_volatile noattr) false)
        | _ => false
        end
    | _ => false
    end.

Fixpoint list_ma_expr_to_ma_exprlist (es: list CInstr.ma_expr): option CInstr.ma_exprlist := 
    match es with 
    | [] => None
    | e::nil => Some (CInstr.MAsingleton e)
    | e :: es' => 
        match list_ma_expr_to_ma_exprlist es' with 
        | Some es' => Some (CInstr.MAcons e es')
        | None => None
        end
    end.

Fixpoint convert_arr_access_helper (expr: Csyntax.expr) (affs: list CInstr.ma_expr) (ctxt: PTree.t nat) (base_ty: CTy.CTy.basetype): result CInstr.arr_access := 
    match expr with 
    | Csyntax.Evar id ty =>
        (* if type_eqb ty base_ty then  *)
        match list_ma_expr_to_ma_exprlist affs with 
        | None => Err "convert_arr_access no index" 
        | Some affs => Okk (CInstr.Aarr id affs base_ty)
        end 
        (* else Err "convert arr access failed, base type not match" *)
    | Csyntax.Ederef (Ebinop Oadd r1 r2 (Tpointer ty noattr)) ty' => 
        if negb (type_eqb ty ty') then Err "convert_arr_access_helper type error" 
        else 
            match convert_aff_expr_cinstr_ma_expr r2 ctxt with 
            | Okk r2 => convert_arr_access_helper r1 (r2 :: affs) ctxt base_ty
            | Err msg => Err msg
            end
    | _ => Err "convert arr access failed"%string
    end.

(** 1.2 convert arr access (R/W of variable/arrays to cinstr arr_access ) *)
Definition convert_arr_access (expr: Csyntax.expr)  (ctxt: PTree.t nat): result CInstr.arr_access := 
    match expr with 
    | Csyntax.Evar id ty => 
        if type_eqb ty type_int32s then 
    Okk (CInstr.Avar id CTy.CTy.int32s) else Err "not int32s"%string
        (** pure variable *)
    | Csyntax.Ederef _ ty => 
    if type_eqb ty type_int32s then 
        convert_arr_access_helper expr [] ctxt CTy.CTy.int32s
        else Err "not int32s arr"%string
    | _ => Err "convert arr access failed"%string
    end.

(** 1.3 convert arr access expression (rhs of assign instruction) to cinstr expression *)
Fixpoint convert_arr_expr (expr: Csyntax.expr) (ctxt: PTree.t nat): result CInstr.expr := 
    match expr with 
    | Csyntax.Eval v ty => 
    if type_eqb ty type_int32s then 
        Okk (CInstr.Eval v CTy.CTy.int32s) else Err "not int32s Eval"%string
    | Csyntax.Evar id ty => 
    if type_eqb ty type_int32s then 
        Okk (CInstr.Eaccess (CInstr.Avar id CTy.CTy.int32s) CTy.CTy.int32s)
    else Err "not int32s Evar"%string
    | Csyntax.Eunop op e ty => 
    if type_eqb ty type_int32s then 
        match convert_arr_expr e ctxt with 
        | Okk e => Okk (CInstr.Eunop op e CTy.CTy.int32s)
        | _ => Err "convert arr unexpr failed"%string
        end
    else Err "not int32s Eunop"%string
    | Csyntax.Ebinop op e1 e2 ty => 
    if type_eqb ty type_int32s then
        match convert_arr_expr e1 ctxt, convert_arr_expr e2 ctxt with 
        | Okk e1, Okk e2 => Okk (CInstr.Ebinop op e1 e2 CTy.CTy.int32s)
        | _, _ => Err "convert arr biexpr failed"%string
        end
    else Err "not int32s Ebinop"%string
    (* | Csyntax.Eseqand e1 e2 ty => 
        match convert_arr_expr e1 ctxt, convert_arr_expr e2 ctxt with 
        | Okk e1, Okk e2 => Okk (CInstr.Eseqand e1 e2 ty)
        | _, _ => Err "convert arr seqand failed"%string
        end
    | Csyntax.Eseqor e1 e2 ty => 
        match convert_arr_expr e1 ctxt, convert_arr_expr e2 ctxt with 
        | Okk e1, Okk e2 => Okk (CInstr.Eseqor e1 e2 ty)
        | _, _ => Err "convert arr seqor failed"%string
        end *)
    | Csyntax.Ederef e ty => 
        match convert_arr_access expr ctxt with 
        | Okk e => 
        if type_eqb ty type_int32s then 
            Okk (CInstr.Eaccess e CTy.CTy.int32s)
        else Err "not int32s Ederef"%string
        | Err msg => Err msg
        end
    | _ => Err "convert arr expr failed"%string
    end.

(** $1[$2+1][$2+$3] + $4 + 5*)
Definition sample_csyntax_arr_access_expr_1 := 
    (Csyntax.Ebinop (Cop.Oadd) 
        (Csyntax.Ebinop (Cop.Oadd)
            (Csyntax.Eindex 
                (Csyntax.Eindex 
                    (Csyntax.Evar 1%positive (Tpointer (Tpointer type_int32s noattr) noattr)) 
                    (Csyntax.Ebinop (Cop.Oadd) (Csyntax.Evar 2%positive type_int32s) (Csyntax.Eval (Values.Vint (Int.one)) type_int32s)  type_int32s)
                (Tpointer type_int32s noattr)) 
                (Csyntax.Ebinop (Cop.Oadd) (Csyntax.Evar 2%positive type_int32s) (Csyntax.Evar 3%positive type_int32s)  type_int32s)  type_int32s
            )
        (Csyntax.Evar 4%positive type_int32s)
        type_int32s
        ) 
    (Csyntax.Eval (Values.Vint (Int.repr 5)) type_int32s)  type_int32s). 
    

Example test_convert_arr_expr: 
    convert_arr_expr 
    sample_csyntax_arr_access_expr_1
    (PTree_Properties.of_list [(2%positive, 2%nat); (3%positive, 3%nat)]) 
    = Okk
    (* $1[$2+1][$2+$3] + $4 + 5 *)
    (CInstr.Ebinop Oadd
    (* $1[$2+1][$2+$3] + $4*)
    (CInstr.Ebinop Oadd
    (*$1[$2+1][$2+$3]*)
       (CInstr.Eaccess
          (*$1*)
          (CInstr.Aarr 1%positive
             (CInstr.MAcons
                (*$2+1*)
                (CInstr.MAbinop Oadd (CInstr.MAvarz 2)
                   (CInstr.MAval (Z.one)))
                (CInstr.MAsingleton
                (*$2+$3*)
                   (CInstr.MAbinop Oadd
                      (CInstr.MAvarz 2)
                      (CInstr.MAvarz 3))))
             CTy.CTy.int32s) CTy.CTy.int32s)
        (*$4*)
       (CInstr.Eaccess (CInstr.Avar 4%positive CTy.CTy.int32s) CTy.CTy.int32s) CTy.CTy.int32s)
    (* 5 *)
    (CInstr.Eval (Values.Vint (Int.repr 5)) CTy.CTy.int32s) CTy.CTy.int32s).
Proof. 
    simpl. 
    rewrite type_eqb_refl; simpl.
    rewrite type_eqb_refl; simpl.
    reflexivity.
Qed.

(** 1.4 convert top-level assign instruction to cinstr assign instruction *)
Definition convert_assign (expr: Csyntax.expr) (ctxt: PTree.t nat): 
    result CInstr.t := 
    match expr with 
    | Csyntax.Eassign l r ty =>
        match convert_arr_access l ctxt, convert_arr_expr r ctxt with
        | Okk l, Okk r => Okk (CInstr.Iassign l r)
        | _, _ => Err "convert assign failed"%string
        end
    | _ => Err "convert assign failed"%string
    end.

(** 2. Csyntax structure to Loop *)
(** 2.1 loop lb/ub, guard test expression convert to Loop expr *)
Fixpoint convert_aff_expr (expr: Csyntax.expr) (ctxt: PTree.t nat): result CPolIRs.Loop.expr := 
    match expr with 
    | Csyntax.Eval v ty => 
        match v with 
        | Values.Vint n => 
            Okk (CPolIRs.Loop.Constant (Int.signed n))
        | _ => Err "convert_aff_expr Vconst failed"%string
        end
    | Csyntax.Evar id ty => 
        match ctxt!id with 
        | Some n => Okk (CPolIRs.Loop.Var n)
        | _ => Err "convert_aff_expr Evar failed"%string
        end
    | Csyntax.Ebinop Cop.Oadd e1 e2 ty => 
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with
        | Okk e1, Okk e2 => Okk (CPolIRs.Loop.Sum e1 e2)
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end
    | Csyntax.Ebinop Cop.Osub e1 e2 ty => 
        (** TODO: Loop lack of Sub, need elaborate on -ax to support more program *)
        (** like, further simplify (-a1) * (a2) x *)
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with
        | Okk e1, Okk e2 => Okk (CPolIRs.Loop.Sum e1 (CPolIRs.Loop.Mult (-1%Z) e2))
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end
    | Csyntax.Ebinop Cop.Omul (Csyntax.Eval (Values.Vint v) ty) e2 ty' => 
        match convert_aff_expr e2 ctxt with
        | Okk e2 => Okk (CPolIRs.Loop.Mult (Int.signed v) e2)
        | Err msg => Err msg
        end
    | Csyntax.Ebinop Cop.Omul e2 (Csyntax.Eval (Values.Vint v) ty) ty' => 
        match convert_aff_expr e2 ctxt with
        | Okk e2 => Okk (CPolIRs.Loop.Mult (Int.signed v) e2)
        | Err msg => Err msg
        end
    | Csyntax.Ebinop Cop.Odiv e1 (Csyntax.Eval (Values.Vint v) ty) ty' => 
        match convert_aff_expr e1 ctxt with
        | Okk e1 => Okk (CPolIRs.Loop.Div e1 (Int.signed v))
        | Err msg => Err msg
        end
    | Csyntax.Ebinop Cop.Omod e1 (Csyntax.Eval (Values.Vint v) ty) ty' => 
        match convert_aff_expr e1 ctxt with
        | Okk e1 => Okk (CPolIRs.Loop.Mod e1 (Int.signed v))
        | Err msg => Err msg
        end
    | _ => Err "not supported may-affine expression (Loop)"%string
    end .

(* 2*$2 + $3 + $4 *)
Definition sample_csyntax_expr:= 
    Csyntax.Ebinop Cop.Oadd
    (Csyntax.Ebinop Cop.Oadd
        (Csyntax.Ebinop Cop.Omul
            (Csyntax.Eval (Values.Vint (Int.repr 2)) type_int32s)
            (Csyntax.Evar 2%positive type_int32s) type_int32s)
        (Csyntax.Evar 3%positive type_int32s) type_int32s)
    (Csyntax.Evar 4%positive type_int32s) type_int32s.

Example test_convert_aff_expr: 
    convert_aff_expr 
        sample_csyntax_expr     
        (PTree_Properties.of_list [(2%positive, 2%nat); (3%positive, 3%nat); (4%positive, 4%nat)])
    = Okk
    (CPolIRs.Loop.Sum
       (CPolIRs.Loop.Sum
          (CPolIRs.Loop.Mult 2%Z (CPolIRs.Loop.Var 2))
          (CPolIRs.Loop.Var 3)) (CPolIRs.Loop.Var 4)).
Proof. simpl. reflexivity. Qed.

(** 2.2 loop guard test expression convert to Loop test *) 

Fixpoint convert_bexpr_to_test (expr: Csyntax.expr) (ctxt: PTree.t nat): result CPolIRs.Loop.test := 
    match expr with 
    | Csyntax.Eval v ty => 
        match v with 
        | Values.Vint n => 
            Okk (CPolIRs.Loop.TConstantTest (negb (Int.eq n Int.zero)))
        | _ => Err "convert_bexpr_to_test Vconst failed"%string
        end
    | Csyntax.Ebinop Cop.Ole e1 e2 ty => 
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (CPolIRs.Loop.LE e1 e2)
        | _, _ => Err "convert_bexpr_to_test Ole failed"%string
        end
    | Csyntax.Ebinop Cop.Olt e1 e2 ty => 
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (CPolIRs.Loop.LE (e1) (CPolIRs.Loop.make_sum e2 (CPolIRs.Loop.Constant 1%Z)))
        | _, _ => Err "convert_bexpr_to_test Olt failed"%string
        end
    | Csyntax.Ebinop Cop.Oge e1 e2 ty =>
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (CPolIRs.Loop.LE e2 e1)
        | _, _ => Err "convert_bexpr_to_test Oge failed"%string
        end
    | Csyntax.Ebinop Cop.Ogt e1 e2 ty => 
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (CPolIRs.Loop.LE (CPolIRs.Loop.make_sum e2 (CPolIRs.Loop.Constant 1%Z)) e1)
        | _, _ => Err "convert_bexpr_to_test Ogt failed"%string
        end
    | Csyntax.Ebinop Cop.Oeq e1 e2 ty => 
        match convert_aff_expr e1 ctxt, convert_aff_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (CPolIRs.Loop.EQ e1 e2)
        | _, _ => Err "convert_bexpr_to_test Olt failed"%string
        end
    | Csyntax.Ebinop Cop.Oand t1 t2 ty => 
        match convert_bexpr_to_test t1 ctxt, convert_bexpr_to_test t2 ctxt with 
        | Okk t1, Okk t2 => 
            Okk (CPolIRs.Loop.And t1 t2)
        | _, _ => Err "convert_bexpr_to_test Olt failed"%string
        end
    | Csyntax.Ebinop Cop.Oor t1 t2 ty =>
        match convert_bexpr_to_test t1 ctxt, convert_bexpr_to_test t2 ctxt with 
        | Okk t1, Okk t2 => 
            Okk (CPolIRs.Loop.Or t1 t2)
        | _, _ => Err "convert_bexpr_to_test Olt failed"%string
        end
    | Csyntax.Eunop Cop.Onotbool t ty => 
        match convert_bexpr_to_test t ctxt with 
        | Okk t => 
            Okk (CPolIRs.Loop.Not t)
        | _ => Err "convert_bexpr_to_test Olt failed"%string
        end
    | _ => Err "not implemented"%string
    end.

Example test_convert_bexpr_to_test: 
    convert_bexpr_to_test 
        (Csyntax.Ebinop Cop.Ole
            (Csyntax.Evar 2%positive type_int32s)
            (Csyntax.Evar 3%positive type_int32s) type_int32s)
        (PTree_Properties.of_list [(2%positive, 2%nat); (3%positive, 3%nat)])
    = Okk (CPolIRs.Loop.LE (CPolIRs.Loop.Var 2) (CPolIRs.Loop.Var 3)).
Proof. simpl. reflexivity. Qed.

Definition create_id_assign_expr_list (depth: nat): list CPolIRs.Loop.expr := 
    map (fun n => CPolIRs.Loop.Var n) (Misc.n_range depth). 

Fixpoint convert_cstmt (stmt: Csyntax.statement) (ctxt: PTree.t nat) (depth: nat): result CPolIRs.Loop.stmt := 
    match stmt with 
    | Csyntax.Sskip => Okk (CPolIRs.Loop.Instr CInstr.Iskip nil) 
    | Csyntax.Sdo e => 
        match convert_assign e ctxt with 
        | Okk instr => Okk (CPolIRs.Loop.Instr instr (create_id_assign_expr_list depth))
        | Err msg => Err msg 
        end
    | Csyntax.Ssequence s1 s2 => 
        match convert_cstmt s1 ctxt depth, convert_cstmt s2 ctxt depth with 
        | Okk s1, Okk (CPolIRs.Loop.Seq s2) => 
            Okk (CPolIRs.Loop.Seq (CPolIRs.Loop.SCons s1 s2))
        | Okk s1, Okk s2 => 
            Okk (CPolIRs.Loop.Seq (CPolIRs.Loop.SCons s1 (CPolIRs.Loop.SCons s2 CPolIRs.Loop.SNil)))
        | _, _ => Err "convert_cstmt Ssequence failed"%string
        end
    | Csyntax.Sifthenelse e s1 s2 => 
        match convert_bexpr_to_test e ctxt, convert_cstmt s1 ctxt depth, convert_cstmt s2 ctxt depth with 
        | Okk tst, Okk s1, Okk s2 => 
            Okk (CPolIRs.Loop.Seq 
                    (CPolIRs.Loop.SCons
                    (CPolIRs.Loop.Guard tst s1) 
                    (CPolIRs.Loop.SCons (CPolIRs.Loop.Guard (CPolIRs.Loop.make_not tst) s2) CPolIRs.Loop.SNil))
                    )
        | _, _, _ => Err "convert_cstmt Sifthenelse failed"%string
        end
    | Csyntax.Sfor s1 e s2 s3 => 
        match s1, e, s2 with
        | Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar id1 ty1) (e) ty1'),
          Csyntax.Ebinop Cop.Olt (Csyntax.Evar id2 ty2) (e') ty2', 
          Csyntax.Sdo (Csyntax.Epostincr Cop.Incr (Csyntax.Evar id3 ty3) ty3') => 
          if andb (Pos.eqb id1 id2) (Pos.eqb id2 id3) then
            if (check_type_int32s ty1) && (check_type_int32s ty1') 
                (* && (check_type_int32s ty2) && (check_type_int32s ty2') *)
                && (check_type_int32s ty3) && (check_type_int32s ty3') then 
            let ctxt' := PTree.set id1 depth ctxt in
            match convert_aff_expr e ctxt', convert_aff_expr e' ctxt', convert_cstmt s3 ctxt' (S depth) with 
            | Okk lb, Okk ub, Okk s3 => 
                Okk 
                (CPolIRs.Loop.Loop lb ub s3)
            | Err msg, _, _ => Err ("convert_cstmt Sfor failed (case1), lb, " ++ msg)
            | _, Err msg, _ => Err ("convert_cstmt Sfor failed (case1), ub," ++ msg)
            | _, _, Err msg => Err ("convert_cstmt Sfor failed (case1), s3," ++ msg)
            end
            else Err "convert_cstmt Sfor failed (case2)"%string
          else Err "convert_cstmt Sfor failed (case3)"%string
        | _, _, _ => Err "convert_cstmt Sfor failed (case4)"%string
        end
    | _ => Err "not implemented"%string
    end.

(** input: affine-position-related expression *)
(** in fact, only Evar/Ebinop/Eunop/Ederef/and/or are allowed *)
(** can be more detail cased: binary test, affine expression*)
Fixpoint collect_cexpr_varinfo (e: Csyntax.expr) (varctxt: list ident) (iters: list ident) (vars: list ident): (list ident*list ident*list ident) := 
    match e with
    | Csyntax.Eval id ty => 
        (varctxt, iters, vars)
    | Csyntax.Evar id ty => 
        if Nat.ltb 0%nat (List.count_occ Pos.eq_dec vars id) then (varctxt, iters, vars) else
            (id :: varctxt, iters, id :: vars)
    | Csyntax.Ebinop _ e1 e2 ty => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars'
    | Csyntax.Eunop _ e ty => 
        collect_cexpr_varinfo e varctxt iters vars
    (* | Csyntax.Ederef e ty => 
        collect_cexpr_varinfo e varctxt iters vars *)
    (* | Csyntax.Eaddrof e ty => 
        collect_cexpr_varinfo e varctxt iters vars *)
    | Csyntax.Eseqand e1 e2 _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars' 
    | Csyntax.Eseqor e1 e2 _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars' 
    (* | Csyntax.Econdition e1 e2 e3 _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        let '(varctxt'', iters'', vars'') := collect_cexpr_varinfo e2 varctxt' iters' vars' in 
        collect_cexpr_varinfo e3 varctxt'' iters'' vars'' *)
    (* | Csyntax.Eassign e1 e2 _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars'  *)
    (* | Csyntax.Eassignop _ e1 e2 _ _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars'  *)
    (* | Csyntax.Epostincr _ e _ => 
        collect_cexpr_varinfo e varctxt iters vars *)
    (* | Csyntax.Ecomma e1 e2 _ => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars'  *)
    (* | Csyntax.Eparen e _  _ => 
        collect_cexpr_varinfo e varctxt iters vars *)
    | _ => (nil, nil, nil)
    end.

(** should be array assign expression, with side-effect-free operators *)
Fixpoint collect_eindex_varinfo (e: Csyntax.expr) (varctxt: list ident) (iters: list ident) (vars: list ident): (list ident * list ident * list ident) := 
    match e with 
    (** base case for array access, the base pointer *)
    | Csyntax.Evar id _ => 
        if Nat.ltb 0%nat (List.count_occ Pos.eq_dec vars id) then (varctxt, iters, vars) else
            (varctxt, iters, id :: vars)
    (** inductive case for array access, a[]..[i]..[]; i should be affine expression *)
    | Csyntax.Ederef (Csyntax.Ebinop Cop.Oadd e1 e2 _) _ =>
        let '(varctxt', iters', vars') := collect_eindex_varinfo e1 varctxt iters vars in 
        collect_cexpr_varinfo e2 varctxt' iters' vars'
    | Csyntax.Ebinop _ e1 e2 ty => 
        let '(varctxt', iters', vars') := collect_eindex_varinfo e1 varctxt iters vars in 
        collect_eindex_varinfo e2 varctxt' iters' vars'
    | Csyntax.Eunop _ e ty =>
        collect_eindex_varinfo e varctxt iters vars
    | _ => (nil, nil, nil)
    end.

(** should be array assign statement *)
Fixpoint collect_assign_rhs_varinfo (e: Csyntax.expr) (varctxt: list ident) (iters: list ident) (vars: list ident): (list ident * list ident * list ident) := 
    match e with 
    | Csyntax.Evar id ty => 
        if Nat.ltb 0%nat (List.count_occ Pos.eq_dec vars id) then (varctxt, iters, vars) else
            (varctxt, iters, id :: vars)
    | Csyntax.Ebinop _ e1 e2 ty => 
        let '(varctxt', iters', vars') := collect_assign_rhs_varinfo e1 varctxt iters vars in 
        collect_assign_rhs_varinfo e2 varctxt' iters' vars'
    | Csyntax.Eunop _ e ty =>
        collect_assign_rhs_varinfo e varctxt iters vars
    | Csyntax.Ederef e' ty =>
        collect_eindex_varinfo e varctxt iters vars
    | _ => (nil, nil, nil)
    end.

Definition collect_opaque_cexpr_varinfo (e: Csyntax.expr) (varctxt: list ident) (iters: list ident) (vars: list ident): (list ident*list ident*list ident) := 
    match e with 
    | Csyntax.Eassign l r _ => 
        let '(varctxt', iters', vars') := collect_eindex_varinfo l varctxt iters vars in
        collect_assign_rhs_varinfo r varctxt' iters' vars' 
    | _ => (nil, nil, nil)
    end.

(** varctxt (variables exist in affine related expression, loop's lb/ub, if guard, array index), iters (all iterators), vars (all variables) *)
Fixpoint collect_cstmt_varinfo (cstmt: Csyntax.statement) (varctxt: list ident) (iters: list ident) (vars: list ident): (list ident * list ident * list ident) := 
    match cstmt with 
    | Csyntax.Sskip => (varctxt, iters, vars)
    | Csyntax.Sdo e => collect_opaque_cexpr_varinfo e varctxt iters vars
    | Csyntax.Ssequence s1 s2 => 
        let '(varctxt', iters', vars') := collect_cstmt_varinfo s1 varctxt iters vars in 
        collect_cstmt_varinfo s2 varctxt' iters' vars'
    | Csyntax.Sifthenelse e s1 s2 => 
        let '(varctxt', iters', vars') := collect_cexpr_varinfo e varctxt iters vars in 
        let '(varctxt'', iters'', vars'') := collect_cstmt_varinfo s1 varctxt' iters' vars' in 
        collect_cstmt_varinfo s2 varctxt'' iters'' vars'' 
    | Csyntax.Sfor s1 e s2 s3 => 
        match s1, e, s2 with
        | Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar id1 ty1) (e) _),
          Csyntax.Ebinop Cop.Olt (Csyntax.Evar id2 _) (e') _, 
          Csyntax.Sdo (Csyntax.Epostincr Cop.Incr (Csyntax.Evar id3 _) _) => 
            if andb (Pos.eqb id1 id2) (Pos.eqb id2 id3) then
                let iters := id1 :: iters in 
                let vars := id1 :: vars in 
                let '(varctxt', iters', vars') := collect_cexpr_varinfo e varctxt iters vars in 
                let '(varctxt'', iters'', vars'') := collect_cexpr_varinfo e' varctxt' iters' vars' in 
                collect_cstmt_varinfo s3 varctxt'' iters'' vars''                 
            else (** should not be here *)
                (nil, nil, nil)
        | _, _, _ => (** should not be here*) 
            (nil, nil, nil)
        end
    | _ => (nil, nil, nil) 
    (* | _ => (varctxt, iters, vars)  *)
        (* should not goes here *)
    end
.

Example test_collect_cstmt_varinfo: 
    (** for($1=0; $1<10; $1++) {$2 = $2 + $1} *)
    let s := Csyntax.Sfor 
        (Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar 1%positive type_int32s) (Csyntax.Eval (Values.Vint Int.zero) type_int32s) type_int32s)) 
        (Csyntax.Ebinop Cop.Olt (Csyntax.Evar 1%positive type_int32s) (Csyntax.Eval (Values.Vint (Int.repr 10%Z)) type_int32s) type_int32s) 
        (Csyntax.Sdo (Csyntax.Epostincr Cop.Incr (Csyntax.Evar 1%positive type_int32s) type_int32s)) 
        (Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar 2%positive type_int32s) (Csyntax.Ebinop Cop.Oadd (Csyntax.Evar 2%positive type_int32s) (Csyntax.Evar 1%positive type_int32s) type_int32s) type_int32s)) in 
    let '(varctxt, iters, vars) := collect_cstmt_varinfo s [] [] [] in 
    (varctxt, iters, vars) = ([], [1%positive], [2%positive; 1%positive]).
Proof. simpl. reflexivity. Qed.

Definition converter (cstmt: Csyntax.statement): result CPolIRs.Loop.t
:= 
    (** should calculate varctxt, ctxt first *)
    let '(varctxt, iters, vars) := collect_cstmt_varinfo cstmt [] [] [] in 
    let ctxt := PTree_Properties.of_list (List.combine varctxt (n_range (List.length varctxt))) in
    match convert_cstmt cstmt ctxt (List.length varctxt) with 
    | Okk cloop => 
        Okk ( cloop, varctxt, map (fun var => (var, CPolIRs.Ty.dummy_arrtype)) vars )
    | Err msg => Err msg
    end.

(* 
        for($1=0; $1<$10; $1++) {
            for($2=0; $2<$1; $2++) {
                $4[$1][$2] = $5[$1][$2] + $6[$1][$2]
            }
        }
        ([10%positivew], [2%positive; 1%positive],
      [6%positive; 5%positive; 4%positive; 2%positive; 1%positive])
*)
Definition sample_csyntax_loop_nests := (Csyntax.Sfor 
(Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar 1%positive type_int32s) (Csyntax.Eval (Values.Vint Int.zero) type_int32s) type_int32s))
(Csyntax.Ebinop Cop.Olt (Csyntax.Evar 1%positive type_int32s) (Csyntax.Evar 10%positive type_int32s) type_bool)
(Csyntax.Sdo (Csyntax.Epostincr Cop.Incr (Csyntax.Evar 1%positive type_int32s) type_int32s))
(Csyntax.Sfor 
    (Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar 2%positive type_int32s) (Csyntax.Eval (Values.Vint Int.zero) type_int32s) type_int32s))
    (Csyntax.Ebinop Cop.Olt (Csyntax.Evar 2%positive type_int32s) (Csyntax.Evar 1%positive type_int32s) type_bool)
    (Csyntax.Sdo (Csyntax.Epostincr Cop.Incr (Csyntax.Evar 2%positive type_int32s) type_int32s))
    (Csyntax.Sdo 
        (Csyntax.Eassign 
            (Csyntax.Eindex (Csyntax.Eindex (Csyntax.Evar 4%positive (Tpointer (Tpointer type_int32s noattr) noattr)) (Csyntax.Evar 1%positive type_int32s) (Tpointer type_int32s noattr)) (Csyntax.Evar 2%positive type_int32s) type_int32s)
                (Csyntax.Ebinop Cop.Oadd 
                    (Csyntax.Eindex (Csyntax.Eindex (Csyntax.Evar 5%positive (Tpointer (Tpointer type_int32s noattr) noattr)) (Csyntax.Evar 1%positive type_int32s) (Tpointer type_int32s noattr)) (Csyntax.Evar 2%positive type_int32s) type_int32s)
                    (Csyntax.Eindex (Csyntax.Eindex (Csyntax.Evar 6%positive (Tpointer (Tpointer type_int32s noattr) noattr)) (Csyntax.Evar 1%positive type_int32s) (Tpointer type_int32s noattr)) (Csyntax.Evar 2%positive type_int32s) type_int32s)
                type_int32s) 
         type_int32s)))
).

Example test_converter: 
    converter sample_csyntax_loop_nests = 
    Okk
    (** varctxt: [$10] => Var 0 *)
    (*
        Loop (Var 1, 0, $0($10)) 
            Loop (Var 2, 0, Var 1) 
                $4[Var 1][Var 2] = $5[Var 1][Var 2] + $6[Var 1][Var 2]
    *)
    (CPolIRs.Loop.Loop (CPolIRs.Loop.Constant (Int.signed Int.zero)) (CPolIRs.Loop.Var 0)
        (CPolIRs.Loop.Loop (CPolIRs.Loop.Constant (Int.signed Int.zero)) (CPolIRs.Loop.Var 1)
            (CPolIRs.Loop.Instr
            (CInstr.Iassign
                (CInstr.Aarr 4%positive
                    (CInstr.MAcons (CInstr.MAvarz 1)
                        (CInstr.MAsingleton (CInstr.MAvarz 2)))
                        CTy.CTy.int32s)
                (CInstr.Ebinop Oadd
                    (CInstr.Eaccess
                        (CInstr.Aarr 5%positive
                        (CInstr.MAcons (CInstr.MAvarz 1)
                            (CInstr.MAsingleton (CInstr.MAvarz 2)))CTy.CTy.int32s)CTy.CTy.int32s)
                    (CInstr.Eaccess
                        (CInstr.Aarr 6%positive
                        (CInstr.MAcons (CInstr.MAvarz 1)
                            (CInstr.MAsingleton (CInstr.MAvarz 2)))
                            CTy.CTy.int32s) CTy.CTy.int32s) CTy.CTy.int32s))
            (create_id_assign_expr_list 3))), [10%positive],
            [(6%positive, CPolIRs.Ty.dummy_arrtype); 
            (5%positive, CPolIRs.Ty.dummy_arrtype); 
            (4%positive, CPolIRs.Ty.dummy_arrtype); 
            (2%positive, CPolIRs.Ty.dummy_arrtype); 
            (10%positive, CPolIRs.Ty.dummy_arrtype); 
            (1%positive, CPolIRs.Ty.dummy_arrtype)])    .
Proof. simpl. unfold converter; simpl. 
        rewrite type_eqb_refl; simpl.
        rewrite type_eqb_refl; simpl.
        reflexivity.
Qed.

(** TODO: simplify and sort the affine expression, Loop & CInstr *)


(******************************************************)
(*********** Reconvert CLoop to Csyntax ***************)
(******************************************************)

(*** reconvert CLoop to Csyntax representation *)
(** We change all Var n into nth variable of its context *)
(** The constant variables ident do not change, and each loop is create with *)
(** a new free ident (will be implemented in ocaml) *)

(* Parameter free_ident: unit -> ident. *)

Fixpoint maexpr_to_csyntax (e: CInstr.ma_expr) (ctxt: list ident): option Csyntax.expr := 
    match e with 
    | CInstr.MAval v => Some (Csyntax.Eval (Values.Vint (Int.repr v)) type_int32s) 
    | CInstr.MAvarz n => 
        match nth_error ctxt n with 
        | Some id' => Some (Csyntax.Evar id' type_int32s)
        | None => None 
        end
    | CInstr.MAunop op r => 
        match maexpr_to_csyntax r ctxt with
        | Some r' => Some (Csyntax.Eunop op r' type_int32s)
        | None => None 
        end  
    | CInstr.MAbinop op r1 r2 => 
        match maexpr_to_csyntax r1 ctxt, maexpr_to_csyntax r2 ctxt with
        | Some r1', Some r2' => Some (Csyntax.Ebinop op r1' r2' type_int32s)
        | _, _ => None 
        end 
    end.

Fixpoint arr_access_to_csyntax_helper (id: ident) (es: list CInstr.ma_expr) (ty: type) (ctxt: list ident): option Csyntax.expr :=
    match es with 
    | nil => Some (Csyntax.Evar id ty)
    | e'::es' => 
        match arr_access_to_csyntax_helper id es' (Tpointer ty noattr) ctxt, maexpr_to_csyntax e' ctxt with
        | Some e, Some e' => Some (Csyntax.Eindex e e' ty)
        | _, _ => None 
        end 
    end.



Fixpoint ma_exprlist_to_list (es: CInstr.ma_exprlist): list CInstr.ma_expr :=
    match es with 
    | CInstr.MAcons e es' => e :: ma_exprlist_to_list es'
    | CInstr.MAsingleton e => e :: nil 
    end.

Definition arr_access_to_csyntax (a: CInstr.arr_access) (ctxt: list ident): option Csyntax.expr :=
    match a with 
    | CInstr.Avar id ty => Some (Csyntax.Evar id type_int32s)
    | CInstr.Aarr id es ty => 
        arr_access_to_csyntax_helper id (List.rev (ma_exprlist_to_list es)) type_int32s ctxt
    end.  

(* $4[$1][$2] *)
Example test_arr_access_to_csyntax: 
    arr_access_to_csyntax (CInstr.Aarr 4%positive
        (CInstr.MAcons (CInstr.MAvarz 1)
            (CInstr.MAsingleton (CInstr.MAvarz 2)))
        (CTy.CTy.int32s)) 
    [999%positive; 1%positive; 2%positive; 3%positive]
        = 
    Some (Csyntax.Eindex (Csyntax.Eindex (Csyntax.Evar 4%positive (Tpointer (Tpointer type_int32s noattr) noattr)) (Csyntax.Evar 1%positive type_int32s) (Tpointer type_int32s noattr)) (Csyntax.Evar 2%positive type_int32s) type_int32s).
Proof. simpl. reflexivity. Qed.
    


Fixpoint cexpr_to_csyntax (e: CInstr.expr) (ctxt: list ident): result Csyntax.expr := 
    match e with 
    | CInstr.Eval v ty => Okk (Csyntax.Eval v type_int32s)
    | CInstr.Evarz n ty => 
        match nth_error ctxt n with
        | Some id' => Okk (Csyntax.Evar id' type_int32s)
        | None => Err "cexpr_to_csyntax Evarz failed"
        end
    | CInstr.Eaccess a ty => 
        match arr_access_to_csyntax a ctxt with 
        | Some e' => Okk e' 
        | None => Err "cexpr_to_csyntax Eaccess failed"
        end
    | CInstr.Eunop op r ty => 
        match cexpr_to_csyntax r ctxt with
        | Okk r' => Okk (Csyntax.Eunop op r' type_int32s)
        | Err msg => Err msg
        end    
    | CInstr.Ebinop op r1 r2 ty => 
        match cexpr_to_csyntax r1 ctxt, cexpr_to_csyntax r2 ctxt with 
        | Okk r1', Okk r2' => Okk (Csyntax.Ebinop op r1' r2' type_int32s)
        | _, _ => Err "cexpr_to_csyntax binop failed"
        end    
    (* | _ => Err "not implemented" *)
    end. 

(** change Transformation into expression *)
(* Definition cexprlist_to_csyntax (es: list CPolIRs.Loop.expr) (ctxt: list ident): result (list Csyntax.expr) := 
    fold_right (fun e acc => 
        match cexpr_to_csyntax e ctxt, acc with 
        | Okk e', Okk acc' => Okk (e' :: acc')
        | Err msg, _ => Err msg
        | _, Err msg => Err msg
        end) (Okk nil) es. *)

Definition cinstr_to_csyntax' (cinstr: CInstr.t) (ctxt: list ident): result Csyntax.statement := 
    match cinstr with 
    | CInstr.Iskip => Okk Csyntax.Sskip 
    | CInstr.Iassign l r => 
        match arr_access_to_csyntax l ctxt, cexpr_to_csyntax r ctxt with
        | Some l', Okk r' => Okk (Csyntax.Sdo (Csyntax.Eassign l' r' (typeof l')))
        | _, _ => Err ""
        end
    end.

Fixpoint loop_expr_to_cinstr_expr (e: CPolIRs.Loop.expr) (ctxt: list ident): option (CInstr.ma_expr) := 
    match e with 
    | CPolIRs.Loop.Constant z => Some (CInstr.MAval z)
    | CPolIRs.Loop.Sum e1 e2 => 
        match loop_expr_to_cinstr_expr e1 ctxt, loop_expr_to_cinstr_expr e2 ctxt with
        | Some e1', Some e2' =>  
            Some (CInstr.MAbinop Cop.Oadd e1' e2')
        | _, _ => None 
        end
    | CPolIRs.Loop.Mult z e => 
        match loop_expr_to_cinstr_expr e ctxt with 
        | Some e' => Some (CInstr.MAbinop Cop.Omul (CInstr.MAval z) e')
        | _ => None 
        end
    | CPolIRs.Loop.Div e z => 
        match loop_expr_to_cinstr_expr e ctxt with 
        | Some e' => Some (CInstr.MAbinop Cop.Odiv e' (CInstr.MAval z))
        | _ => None 
        end
    | CPolIRs.Loop.Mod e z => 
        match loop_expr_to_cinstr_expr e ctxt with 
        | Some e' => Some (CInstr.MAbinop Cop.Omod e' (CInstr.MAval z))
        | _ => None 
        end
    | CPolIRs.Loop.Var n => 
        Some (CInstr.MAvarz n)
    | _ => None
    end.
 
Fixpoint loop_exprlist_to_cinstr_exprlist (es: list CPolIRs.Loop.expr) (ctxt: list ident): option (list CInstr.ma_expr) := 
    match es with 
    | nil => Some nil 
    | e::es' => 
        match loop_exprlist_to_cinstr_exprlist es' ctxt, loop_expr_to_cinstr_expr e ctxt with 
        | Some es'', Some e' => Some (e' :: es'')
        | _, _ => None 
        end
    end.    

Fixpoint cinstr_ma_expr_rewrite (e: CInstr.ma_expr) (es: list CInstr.ma_expr): option CInstr.ma_expr := 
    match e with 
    | CInstr.MAval v => Some e
    | CInstr.MAvarz n => 
        match nth_error es n with 
        | Some e => Some e
        | None => None 
        end
    | CInstr.MAunop op e => 
        match cinstr_ma_expr_rewrite e es with 
        | Some e' => Some (CInstr.MAunop op e')
        | None => None 
        end
    | CInstr.MAbinop op e1 e2 => 
        match cinstr_ma_expr_rewrite e1 es, cinstr_ma_expr_rewrite e2 es with 
        | Some e1', Some e2' => Some (CInstr.MAbinop op e1' e2')
        | _, _ => None 
        end
    end.

Fixpoint cinstr_ma_exprlist_rewrite (el: CInstr.ma_exprlist) (es: list CInstr.ma_expr): option CInstr.ma_exprlist := 
    match el with 
    | CInstr.MAsingleton e => 
        match cinstr_ma_expr_rewrite e es with
        | Some e' => Some (CInstr.MAsingleton e')
        | None => None 
        end
    | CInstr.MAcons e el' => 
        match cinstr_ma_expr_rewrite e es, cinstr_ma_exprlist_rewrite el' es with 
        | Some e', Some el'' => Some (CInstr.MAcons e' el'')
        | _, _ => None 
        end
    end.


Definition cinstr_arr_access_rewrite (a: CInstr.arr_access) (es: list CInstr.ma_expr): option CInstr.arr_access := 
    match a with 
    | CInstr.Avar id ty => Some a 
    | CInstr.Aarr id el ty => 
        match cinstr_ma_exprlist_rewrite el es with
        | Some el' => Some (CInstr.Aarr id el' ty) 
        | None => None 
        end
    end.

(** restricted ma expression to cinstr expr *)
Fixpoint ma_expr_to_cinstr_expr (e: CInstr.ma_expr): CInstr.expr := 
    match e with
    | CInstr.MAval v => CInstr.Eval (Values.Vint (Int.repr v)) CTy.CTy.int32s
    | CInstr.MAvarz n => CInstr.Evarz n CTy.CTy.int32s
    | CInstr.MAunop op e => CInstr.Eunop op (ma_expr_to_cinstr_expr e) CTy.CTy.int32s
    | CInstr.MAbinop op e1 e2 => CInstr.Ebinop op (ma_expr_to_cinstr_expr e1) (ma_expr_to_cinstr_expr e2) CTy.CTy.int32s
    end.

Fixpoint cinstr_arr_expr_rewrite (e: CInstr.expr) (es: list CInstr.ma_expr): option CInstr.expr := 
    let es' := map ma_expr_to_cinstr_expr es in
    match e with 
    | CInstr.Eval v ty => Some e
    | CInstr.Evarz n ty => 
        match nth_error es' n with
        | Some e => Some e
        | None => None 
        end
    | CInstr.Eunop op e ty =>
        match cinstr_arr_expr_rewrite e es with 
        | Some e' => Some (CInstr.Eunop op e' ty)
        | None => None 
        end
    | CInstr.Ebinop op e1 e2 ty =>
        match cinstr_arr_expr_rewrite e1 es, cinstr_arr_expr_rewrite e2 es with 
        | Some e1', Some e2' => Some (CInstr.Ebinop op e1' e2' ty)
        | _, _ => None 
        end
    | CInstr.Eaccess a ty => 
        match cinstr_arr_access_rewrite a es with 
        | Some a' => Some (CInstr.Eaccess a' ty)
        | None => None 
        end
    (* | CInstr.Eseqand e1 e2 ty => 
        match cinstr_arr_expr_rewrite e1 es, cinstr_arr_expr_rewrite e2 es with 
        | Some e1', Some e2' => Some (CInstr.Eseqand e1' e2' ty)
        | _, _ => None 
        end
    | CInstr.Eseqor e1 e2 ty => 
        match cinstr_arr_expr_rewrite e1 es, cinstr_arr_expr_rewrite e2 es with 
        | Some e1', Some e2' => Some (CInstr.Eseqor e1' e2' ty)
        | _, _ => None 
        end *)
    end.



Definition cinstr_rewrite_transformation_helper (cinstr: CInstr.t) (es: list CInstr.ma_expr): option CInstr.t := 
    match cinstr with 
    | CInstr.Iskip => Some cinstr
    | CInstr.Iassign a e => 
        match cinstr_arr_access_rewrite a es, cinstr_arr_expr_rewrite e es with
        | Some a', Some e' => Some (CInstr.Iassign a' e')
        | _, _ => None
        end
    end
.

Definition cinstr_rewrite_transformation (cinstr: CInstr.t) (es: list CPolIRs.Loop.expr) (ctxt: list ident): result (CInstr.t) := 
    match loop_exprlist_to_cinstr_exprlist es ctxt with
    | Some es' => 
        match cinstr_rewrite_transformation_helper cinstr es' with
        | Some cinstr' => Okk cinstr'
        | None => Err "cinstr_rewrite_transformation failed (case1)"
        end
    | None => Err "cinstr_rewrite_transformation failed (case2)"
    end.  

Definition cinstr_to_csyntax (cinstr: CInstr.t) (es: list CPolIRs.Loop.expr) (ctxt: list ident): result Csyntax.statement :=
    match cinstr_rewrite_transformation cinstr es ctxt with 
    | Okk cinstr' => cinstr_to_csyntax' cinstr' ctxt
    | Err msg => Err msg 
    end.    


(** all affine expression are assumed as int32s caculation *)
Fixpoint reconvert_cloop_expr (expr: CPolIRs.Loop.expr) (ctxt: list ident): result Csyntax.expr 
    := 
    match expr with 
    | CPolIRs.Loop.Constant z => 
        Okk (Csyntax.Eval (Values.Vint (Int.repr z)) Ctypes.type_int32s) 
    | CPolIRs.Loop.Sum e1 e2 => 
        match reconvert_cloop_expr e1 ctxt, reconvert_cloop_expr e2 ctxt with
        | Okk e1, Okk e2 => 
            Okk (Csyntax.Ebinop Cop.Oadd e1 e2 Ctypes.type_int32s)
        | _, _ => Err "Reconvert cloop expr Sum failed"%string
        end
    | CPolIRs.Loop.Mult z e => 
        match reconvert_cloop_expr e ctxt with
        | Okk e => 
            Okk (Csyntax.Ebinop Cop.Omul  
                    (Csyntax.Eval (Values.Vint (Int.repr z)) Ctypes.type_int32s) 
                    e Ctypes.type_int32s)
        | _ => Err "Reconvert cloop expr Mult failed"%string
        end
    | CPolIRs.Loop.Div e z => 
        match reconvert_cloop_expr e ctxt with
        | Okk e => 
            Okk (Csyntax.Ebinop Cop.Odiv e 
                    (Csyntax.Eval (Values.Vint (Int.repr z)) Ctypes.type_int32s) 
                    Ctypes.type_int32s)
        | _ => Err "Reconvert cloop expr Div failed"%string
        end
    | CPolIRs.Loop.Mod e z => 
        match reconvert_cloop_expr e ctxt with
        | Okk e => 
            Okk (Csyntax.Ebinop Cop.Omod e 
                    (Csyntax.Eval (Values.Vint (Int.repr z)) Ctypes.type_int32s) 
                    Ctypes.type_int32s)
        | _ => Err "Reconvert cloop expr Mod failed"%string
        end
    | CPolIRs.Loop.Var n => 
        match nth_error ctxt n with 
        | Some id => Okk (Csyntax.Evar id Ctypes.type_int32s)
        | None => Err "Reconvert cloop expr Var failed"%string
        end
    | CPolIRs.Loop.Max e1 e2 => 
        match reconvert_cloop_expr e1 ctxt, reconvert_cloop_expr e2 ctxt with
        | Okk e1, Okk e2 => 
            Okk (Csyntax.Econdition 
                (Csyntax.Ebinop Cop.Oge e1 e2 Ctypes.type_int32s) 
                e1 e2 Ctypes.type_int32s)
        | _, _ => Err "Reconvert cloop expr Max failed"%string
        end
    | CPolIRs.Loop.Min e1 e2 => 
        match reconvert_cloop_expr e1 ctxt, reconvert_cloop_expr e2 ctxt with
        | Okk e1, Okk e2 => 
            Okk (Csyntax.Econdition 
                (Csyntax.Ebinop Cop.Ole e1 e2 Ctypes.type_int32s) 
                e1 e2 Ctypes.type_int32s)
        | _, _ => Err "Reconvert cloop expr Min failed"%string
        end
    end.


Fixpoint reconvert_cloop_test (tst: CPolIRs.Loop.test) (ctxt: list ident): result Csyntax.expr 
:= 
    match tst with 
    | CPolIRs.Loop.LE e1 e2 => 
        match reconvert_cloop_expr e1 ctxt, reconvert_cloop_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (Csyntax.Ebinop Cop.Ole e1 e2 (Ctypes.type_bool))
        | _, _ => Err "Reconvert cloop test LE failed"%string
        end
    | CPolIRs.Loop.EQ e1 e2 => 
        match reconvert_cloop_expr e1 ctxt, reconvert_cloop_expr e2 ctxt with 
        | Okk e1, Okk e2 => 
            Okk (Csyntax.Ebinop Cop.Oeq e1 e2 (Ctypes.type_bool))
        | _, _ => Err "Reconvert cloop test EQ failed"%string
        end
    | CPolIRs.Loop.And tst1 tst2 => 
        match reconvert_cloop_test tst1 ctxt, reconvert_cloop_test tst2 ctxt with
        | Okk tst1, Okk tst2 => 
            Okk (Csyntax.Ebinop Cop.Oand tst1 tst2 (Ctypes.type_bool))
        | _, _ => Err "Reconvert cloop test And failed"%string
        end
    | CPolIRs.Loop.Or tst1 tst2 => 
        match reconvert_cloop_test tst1 ctxt, reconvert_cloop_test tst2 ctxt with
        | Okk tst1, Okk tst2 => 
            Okk (Csyntax.Ebinop Cop.Oor tst1 tst2 (Ctypes.type_bool))
        | _, _ => Err "Reconvert cloop test Or failed"%string
        end
    | CPolIRs.Loop.Not tst => 
        match reconvert_cloop_test tst ctxt with 
        | Okk tst => 
            Okk (Csyntax.Eunop Cop.Onotbool tst (Ctypes.type_bool))
        | _ => Err "Reconvert cloop test Not failed"%string
        end
    | CPolIRs.Loop.TConstantTest b => 
        Okk (Csyntax.Eval (if b then Values.Vtrue else Values.Vfalse) Ctypes.type_bool)
    end.

(** currently, all iterators are assumed as INT32 *)

Definition make_csyntax_assign_stmt (fv: ident) (expr: Csyntax.expr): Csyntax.statement := 
    Csyntax.Sdo (Csyntax.Eassign (Csyntax.Evar fv (Ctypes.type_int32s)) expr (Ctypes.type_int32s)).

Definition make_csyntax_lt_expr (fv: ident) (ub: Csyntax.expr): Csyntax.expr := 
    Csyntax.Ebinop Cop.Olt (Csyntax.Evar fv (Ctypes.type_int32s)) ub (Ctypes.type_bool).

(** currently, we only support increment with stride with one *)
Definition make_incr_stmt (fv: ident): Csyntax.statement := 
    Csyntax.Sdo (Epostincr (Cop.Incr) (Csyntax.Evar fv (Ctypes.type_int32s)) (Ctypes.type_int32s)).

Fixpoint reconvert_cloop (cloop: CPolIRs.Loop.stmt) (ctxt: list ident): result Csyntax.statement := 
    match cloop with 
    | CPolIRs.Loop.Instr i es => cinstr_to_csyntax i es ctxt 
    | CPolIRs.Loop.Seq stmts => 
        reconvert_cloop_stmts stmts ctxt
    | CPolIRs.Loop.Guard tst stmt => 
        match reconvert_cloop stmt ctxt, reconvert_cloop_test tst ctxt with 
        | Okk cstmt, Okk tst => 
            Okk (Csyntax.Sifthenelse tst cstmt Csyntax.Sskip)
        | _, _ => Err "Reconvert cloop guard to csyntax ifthenelse failed"%string
        end 
    | CPolIRs.Loop.Loop lb ub stmt =>
        let fv := free_ident tt in  
        let ctxt' := ctxt ++ [fv] in 
        match reconvert_cloop_expr lb ctxt', reconvert_cloop_expr ub ctxt', reconvert_cloop stmt ctxt' with
        | Okk lb, Okk ub, Okk stmt => 
            Okk (Csyntax.Sfor (make_csyntax_assign_stmt fv lb) (make_csyntax_lt_expr fv ub) (make_incr_stmt fv) stmt)
        | _, _, _ => Err "Reconvert cloop loop to csyntax for failed"%string
        end
    (* | _ => Err "not implemented"%string *)
    end
with reconvert_cloop_stmts (stmts: CPolIRs.Loop.stmt_list) (ctxt: list ident): result Csyntax.statement := 
    match stmts with 
    | CPolIRs.Loop.SNil => Okk (Csyntax.Sskip) 
    | CPolIRs.Loop.SCons stmt CPolIRs.Loop.SNil => 
        match reconvert_cloop stmt ctxt with 
        | Okk cstmt => Okk cstmt
        | Err msg => Err msg
        end
    | CPolIRs.Loop.SCons stmt stmts' => 
        match reconvert_cloop stmt ctxt with 
        | Okk cstmt => 
            match reconvert_cloop_stmts stmts' ctxt with 
            | Okk cstmt' => 
                Okk (Csyntax.Ssequence cstmt cstmt')
            | Err msg => Err msg
            end
        | Err msg => Err msg
        end
    end
. 

Definition reconverter (cloop_ext: CPolIRs.Loop.t): result (Csyntax.statement) 
:= 
    let '(cloop, varctxt, _) := cloop_ext in
    reconvert_cloop cloop varctxt. 

(* Example test_convert_reconvert:
    match converter (sample_csyntax_loop_nests) with 
    | Okk cloop => 
        match reconverter cloop with 
        | Okk csyntax => csyntax = sample_csyntax_loop_nests
        | Err msg => False
        end
    | Err _ => False
    end
.
Proof. simpl. rewrite test_converter. unfold reconverter. unfold reconvert_cloop. simpl.
unfold sample_csyntax_loop_nests. 
    unfold make_csyntax_assign_stmt. unfold make_csyntax_lt_expr. unfold make_incr_stmt.
    econstructor. 

     simpl.
reflexivity. 

unfold converter; simpl. *)
