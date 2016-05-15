Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang TrfState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Open Scope Z_scope.




Section SCtrf.

Variable ops: opSig.

Variable lFun : LeakFun ops.

Definition ok: ident := xH.
Definition okSC: ident := xO xH.
Definition cL: ident := xI xH.
Definition cR: ident := xO (xO xH).
Definition leakL: ident := xH.
(* obs: uma alternativa era registar toda a informação SC no array
    leak[0] = ok
    leak[1] = countL
    leak[2] = countR
    leak[3..] = leakage...
PARECE BOA IDEIA!!! :-)
*)


Parameter regLeak : expr ops -> cmd ops.
Parameter chkLeak : expr ops -> cmd ops.
Parameter initSC: cmd ops.
Parameter chkSC: cmd ops.

Parameter  preleak: expr ops -> seq (expr ops).
Parameter expr_i: bool -> expr ops -> expr ops.
Parameter lvalue_i: bool -> lvalue ops -> lvalue ops.

Fixpoint procLeak (side:bool) (l: seq (expr ops)) : cmd ops :=
 match l, side with
 | [::], _ => @Skip ops
 | e::es, false => Seq (regLeak e) (procLeak side es)
 | e::es, true => Seq (chkLeak e) (procLeak side es)
 end.

Fixpoint mirror (side:bool) (c: cmd ops) {struct c} : cmd ops :=
 match c with
 | Skip => @Skip ops
 | Assert e => Assert (expr_i side e)
 | Assume e => Assume (expr_i side e)
 | Assign x e => Seq (Seq (procLeak side (preleak (expr_i side (ValOf x))))
                          (procLeak side (preleak (expr_i side e))))
                     (Assign (lvalue_i side x) (expr_i side e))
 | Seq c1 c2 => Seq (mirror side c1) (mirror side c2)
 | If b c1 c2 => Seq (Seq (procLeak side (preleak (expr_i side b)))
                          (procLeak side [:: expr_i side b]))
                     (If (expr_i side b) (mirror side c1) (mirror side c2))
 | While b c1 =>
    Seq (Seq (procLeak side (preleak (expr_i side b)))
             (procLeak side [:: expr_i side b]))
        (While (expr_i side b) 
               (Seq (mirror side c1)
                    (Seq (procLeak side (preleak (expr_i side b)))
                         (procLeak side [:: expr_i side b]))))
 end.
                 
Definition selfComp (c: cmd ops) : cmd ops :=
 (Seq (Seq initSC (Seq (mirror false c) (mirror true c))) chkSC).

Parameter cmd_i: bool -> cmd ops -> cmd ops.


Theorem selfComp_A: forall (c:cmd ops) ts1 ts2 (s11 s12 s21 s22: State) l1 l2 l',
 eval_cmd lFun s11 c l1 (Some s21) ->
 eval_cmd lFun s12 c l2 (Some s22) ->
 eval_cmd lFun (joinState ts1 s11 s12) (selfComp c) l' (Some (joinState ts2 s21 s22))
 /\ l1==l2 = true (* ts2[okSC] /\ ok1 = ok2 *).
Admitted.

Theorem selfComp_B: forall (c:cmd ops) ts1 ts2 (s11 s12 s21 s22: State) l1 l2 l',
 eval_cmd lFun (joinState ts1 s11 s12) (selfComp c) l' (Some (joinState ts2 s21 s22)) ->
 eval_cmd lFun s11 c l1 (Some s21) /\
 eval_cmd lFun s12 c l2 (Some s22) /\
 True (* ts2[okSC] = l1==l2 /\ ok1 = ok2 *).
Admitted.



End SCtrf.

