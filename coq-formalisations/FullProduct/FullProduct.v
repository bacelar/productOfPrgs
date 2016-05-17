Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang TrfState SelfComp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Open Scope Z_scope.


Arguments ok_lvalue [ops].
Arguments ok_expr [ops].
Arguments okSC_lvalue [ops].
Arguments okSC_expr [ops].
 
Section FullProductTrf.

Variable ops: opSig.

Definition ok_upd (e: expr ops) : cmd ops :=
 Assign ok_lvalue (And ok_expr e).

Variable lspec: LeakSpec ops.

Definition EqLeak (e1 e2: expr ops): expr ops :=
 EqSeqExpr (preleak lspec e1) (preleak lspec e2).

Lemma isTrue_EqLeak: forall st st1 st2 e,
 isTrue_expr (joinState (st1,st2,st)) (EqLeak (expr_i1 e) (expr_i2 e))
 <-> leak_expr (preleak lspec) st1 e = leak_expr (preleak lspec) st2 e.
Proof.
admit (*
move=> st1 st2 e;
rewrite isTrue_EqSeqExpr /leak_expr !preleak_ren -map_comp.
have ->:[seq eval_expr (joinState st1 st2) (ren_expr id_i1 x)
        | x <- preleak lspec e] = [seq eval_expr st1 x | x <- preleak lspec e].
 by apply eq_map => x; rewrite eval_expr_join_i1.
rewrite -map_comp.
have ->:[seq eval_expr (joinState st1 st2) (ren_expr id_i2 x)
        | x <- preleak lspec e] = [seq eval_expr st2 x | x <- preleak lspec e].
 by apply eq_map => x; rewrite eval_expr_join_i2.
have ->: [seq inr (eval_expr st1 e0) | e0 <- preleak lspec e] =
         map (@inr bool Z) [seq eval_expr st1 x | x <- preleak lspec e] .
 by rewrite map_comp.
have ->: [seq inr (eval_expr st2 e0) | e0 <- preleak lspec e] =
         map (@inr bool Z) [seq eval_expr st2 x | x <- preleak lspec e] .
 by rewrite map_comp.
split => H; first by rewrite H.
have inr_inj: injective (@inr bool Z) by move=> x1 x2 [->].
by apply (inj_map inr_inj).
*).
Qed.

Definition assertEqLeak (e: expr ops): cmd ops :=
 Assert (EqLeak (ren_expr false e) (ren_expr true e)).
Definition assertEqLeakTest (e: expr ops): cmd ops :=
 Assert (And (Equal (IsTrue (ren_expr false e)) (IsTrue (ren_expr true e)))
             (EqLeak (ren_expr false e) (ren_expr true e))).


Fixpoint productTrf (c: cmd ops) {struct c} : cmd ops :=
 match c with
 | Skip => @Skip ops
 | Assert e => Seq (Assert (ren_expr false e)) (Assert (ren_expr true e))
 | Assume e => Seq (Assume (ren_expr false e)) (Assume (ren_expr true e))
 | Assign x e => Seq (Seq (assertEqLeak (ValOf x))
                          (assertEqLeak e))
                     (Seq (Assign (ren_lvalue false x) (ren_expr false e))
                          (Assign (ren_lvalue true x) (ren_expr true e)))
 | Seq c1 c2 => Seq (productTrf c1) (productTrf c2)
 | If b c1 c2 => Seq (assertEqLeakTest b)
                     (If ok_expr
                         (If (ren_expr false b) (productTrf c1) (productTrf c2))
                         (Seq (selfComp lspec (If b c1 c2)) (ok_upd okSC_expr)))
 | While b c1 =>
    Seq (assertEqLeakTest b)
        (Seq (While (And ok_expr (ren_expr false b) )
                    (Seq (productTrf c1)
                         (assertEqLeakTest b)))
             (Seq (selfComp lspec (While b c1)) (ok_upd okSC_expr)))
 end.

Definition initProduct: cmd ops :=
 Assign ok_lvalue (Const _ 1).

Fixpoint assumeVarRestr (v: VarRestr) : cmd ops :=
 match v with
 | [::] => Skip _
 | x::xs => Seq (Assume (Equal (ren_expr false (ValOf (Var _ x))) (ren_expr true (ValOf (Var _ x))))) (assumeVarRestr xs)
 end.

Variable vIN vOUT: VarRestr.

Definition fullProduct (c: cmd ops) : cmd ops :=
 Seq (Seq initProduct (Seq (assumeVarRestr vIN) 
                           (Seq (productTrf c) (assumeVarRestr vOUT))))
     (Assert ok_expr).

Definition trfState0 := mkTrfSt 0 (fun _ => 0).

Definition Safe' lspec (c:cmd ops) :=
 forall st st' l, eval_cmd lspec st c l st' -> st'<>None.
Definition leakSecure' vIN vOUT c :=
 forall s1 s2 l1 l2 ss1 ss2,
   eqstateR vIN s1 s2 ->
   eval_cmd lspec s1 c l1 ss1 ->
   eval_cmd lspec s2 c l2 ss2 ->
   exists s1' s2', ss1 = Some s1' /\ ss2 = Some s2' /\
   (eqstateR vOUT s1' s2' -> l1 = l2).

Theorem fullProduct_sound: forall c,
 Safe' lspec (fullProduct c) ->
 leakSecure' vIN vOUT c.
Proof.
rewrite /leakSecure' => c H s1 s2 l1 l2 ss1 ss2 HIN H1 H2.
move: {H} (H (joinState (s1,s2,trfState0))) => H.
(* ??? tem interesse ???
eqstateR vIN s1 s2 ->
eval_cmd lspec s1 c l1 s1' ->
eval_cmd lspec s2 c l2 s2' ->
eval_cmd lspec (joinState (s1,s2,trfState0)) (fullProduct' c) ss
/\ ss <> None -> s1' <> None /\ s2' <> None.
*)
move: ss1 H1 => [s1'|] H1; last first.
 admit (* H1 -> absurd H 
pq. eval_cmd lspec s1 c l1 None ->
    eval_cmd lspec (joinState (s1, s2, trfState0)) (fullProduct c) ll None
*).
move: ss2 H2 => [s2'|] H2; last first.
 admit (* H2 -> absurd H 
pq. eval_cmd lspec s2 c l2 None ->
    eval_cmd lspec (joinState (s1, s2, trfState0)) (fullProduct c) ll None
*).
exists s1', s2'; split => //.
split => // HOUT.
(* 
 HIN : eqstateR vIN s1 s2
 H1 : eval_cmd lspec s1 c l1 (Some s1')
 H2 : eval_cmd lspec s2 c l2 (Some s2')
 HOUT : eqstateR vOUT s1' s2'
 =======
 exists ll s',
 eval_cmd lspec (joinState (s1, s2, trfState0))
                (fullProduct' c) ll (Some s')
 /\ eval_expr s' ok_expr != 0 -> l1=l2
*)
admit.
Qed.


Theorem fullProduct_complete: forall c,
 leakSecure' vIN vOUT c -> 
 Safe' lspec (fullProduct c).
Proof.
rewrite /Safe' /leakSecure' => c H st.
move => [st'|] l H' => //.
 (* H' -> !assertOK \/ eval_cmd lspec st (fullProduct' c) l None
   (1) -> absurd H
   (2) -> eval_cmd lspec s1 c l1 None \/ eval_cmd lspec s2 c l2 None
   (3,4) -> absurd H
 *)
inversion_clear H'.
 inversion_clear H1.
 admit.
inversion_clear H0; last first.
 admit (* simple *).
inversion_clear H2; last first.
 admit (* simple *).
inversion_clear H3. 
 admit (* simple *).
(* H2 : eval_cmd lspec st0 (productTrf c) l3 ss'
   ===
   eval_cmd lspec s1 c l1 ss1 /\
   eval_cmd lspec s2 c l2 ss2 /\ ss' = Some st' -> ss1 = Some (st'.1.1)...
*)
admit.
Qed.

