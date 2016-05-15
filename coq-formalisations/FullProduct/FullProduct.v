Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang TrfState SelfComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Open Scope Z_scope.




Section FullProductTrf.

Variable ops: opSig.

Variable lFun : LeakFun ops.

Parameter assertEqLeak : expr ops -> cmd ops.
Parameter assertEqExpr : expr ops -> cmd ops.
Parameter ok_get : expr ops.
Parameter okSC_get : expr ops.
Parameter ok_reg : expr ops -> cmd ops.

Fixpoint productTrf (c: cmd ops) {struct c} : cmd ops :=
 match c with
 | Skip => @Skip ops
 | Assert e => Seq (Assert (expr_i false e)) (Assert (expr_i true e))
 | Assume e => Seq (Assume (expr_i false e)) (Assume (expr_i true e))
 | Assign x e => Seq (Seq (assertEqLeak (ValOf x))
                          (assertEqLeak e))
                     (Seq (Assign (lvalue_i false x) (expr_i false e))
                          (Assign (lvalue_i true x) (expr_i true e)))
 | Seq c1 c2 => Seq (productTrf c1) (productTrf c2)
 | If b c1 c2 => Seq (Seq (assertEqLeak b)
                          (assertEqExpr b))
                     (If ok_get
                         (If (expr_i false b) (productTrf c1) (productTrf c2))
                         (Seq (selfComp (If b c1 c2)) (ok_reg okSC_get)))
 | While b c1 =>
    Seq (Seq (assertEqLeak b)
             (assertEqExpr b))
        (Seq (While (And ok_get (expr_i false b) )
                    (Seq (productTrf c1)
                         (Seq (assertEqLeak b)
                              (assertEqExpr b))))
             (Seq (selfComp (While b c1)) (ok_reg okSC_get)))
 end.

Parameter initProduct : cmd ops.
Parameter assumeEqIn : cmd ops.
Parameter assumeEqOut : cmd ops.
Parameter chkOK : cmd ops.


Definition fullProduct (c: cmd ops) : cmd ops :=
 Seq (Seq initProduct (Seq assumeEqIn (productTrf c)))
     (Seq assumeEqOut chkOK).

Parameter cmd_i: bool -> cmd ops -> cmd ops.

(*
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

*)