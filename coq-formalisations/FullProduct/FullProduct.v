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

Definition ok_upd (e: expr ops) : cmd ops :=
 Assign ok_lvalue (And ok_expr e).

Variable lspec: LeakSpec ops.

Definition EqLeak (e1 e2: expr ops): expr ops :=
 EqSeqExpr (preleak lspec e1) (preleak lspec e2).

Lemma isTrue_EqLeak: forall st st1 st2 e,
 isTrue_expr (joinState (st1,st2,st)) (EqLeak (expr_i1 e) (expr_i2 e))
 <-> leak_expr (preleak lspec) st1 e = leak_expr (preleak lspec) st2 e.
Proof.
move=> st st1 st2 e.
rewrite /EqLeak /= isTrue_EqSeqExpr /leak_expr !preleak_ren -map_comp.
have ->:[seq eval_expr (joinState (st1,st2,st)) (ren_expr false x)
        | x <- preleak lspec e] = [seq eval_expr st1 x | x <- preleak lspec e].
 by apply eq_map => x; rewrite eval_expr_join_i1.
rewrite -map_comp.
have ->:[seq eval_expr (joinState (st1,st2,st)) (ren_expr true x)
        | x <- preleak lspec e] = [seq eval_expr st2 x | x <- preleak lspec e].
 by apply eq_map => x; rewrite eval_expr_join_i2.
(*
have ->: [seq inr (eval_expr st1 e0) | e0 <- preleak lspec e] =
         map (@inr bool Z) [seq eval_expr st1 x | x <- preleak lspec e] .
 by rewrite map_comp.
have ->: [seq inr (eval_expr st2 e0) | e0 <- preleak lspec e] =
         map (@inr bool Z) [seq eval_expr st2 x | x <- preleak lspec e] .
 by rewrite map_comp.
*)
split => H; first by rewrite H.
apply H.
(*
have inr_inj: injective (@inr bool Z) by move=> x1 x2 [->].
by apply (inj_map inr_inj).
*)
Qed.

Definition assertEqLeak (e: expr ops): cmd ops :=
 ok_upd (EqLeak (ren_expr false e) (ren_expr true e)).
Definition assertEqLeakTest (e: expr ops): cmd ops :=
 ok_upd (And (Equal (IsTrue (ren_expr false e)) (IsTrue (ren_expr true e)))
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

(* prop1 de fullProduct *)
Lemma product_sound': forall n c s1 s2 st l1 l2 s1' s2',
  feval_cmd lspec n c s1 = Some (Some s1',l1) ->
  feval_cmd lspec n c s2 = Some (Some s2',l2) ->
  exists st' ll,
   eval_cmd lspec (updLValue (joinState (s1, s2, st)) (@ok_lvalue ops) 1)
            (productTrf c)
            ll (Some (joinState (s1',s2',st')))
   /\ (isTrue_expr (joinState (s1',s2',st')) (@ok_expr ops) <-> l1=l2).
Proof.
elim => //=.
move => n IH [|e|e|x e|c1 c2|b c1 c2|b c] s1 s2 st l1 l2 s1' s2' H1 H2.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
Qed.

Lemma product_sound: forall c s1 s2 st l1 l2 s1' s2',
  eval_cmd lspec s1 c l1 (Some s1') ->
  eval_cmd lspec s2 c l2 (Some s2') ->
  exists st' ll,
   eval_cmd lspec (updLValue (joinState (s1, s2, st)) (@ok_lvalue ops) 1)
            (productTrf c)
            ll (Some (joinState (s1',s2',st')))
   /\ (isTrue_expr (joinState (s1',s2',st')) (@ok_expr ops) <-> l1=l2).
Proof.
move=> c s1 s2 st l1 l2 s1' s2'
       /eval_cmd_feval [n1 H1] /eval_cmd_feval [n2 H2].
apply product_sound' with (maxn n1 n2).
 apply feval_cmd_weak with n1 => //.
 by apply leq_maxl.
apply feval_cmd_weak with n2 => //.
by apply leq_maxr.
Qed.

(* prop2 de fullProduct *)
Lemma product_complete: forall c s ll s',
  eval_cmd lspec s (productTrf c) ll (Some s') ->
  exists l1 l2,
   [/\ eval_cmd lspec (splitState s).1.1 c l1 (Some (splitState s').1.1),
       eval_cmd lspec (splitState s).1.2 c l2 (Some (splitState s').1.2)
    & isTrue_expr s (@ok_expr ops) -> l1=l2 -> isTrue_expr s' (@ok_expr ops)].
Proof.
admit.
Qed.

Lemma product_imgN: forall st s1 c l1,
 eval_cmd lspec s1 c l1 None ->
 exists ll,
 eval_cmd lspec (joinState (s1,s1,st)) (productTrf c) ll None.
Proof.
move=> st s1 c l1 /eval_cmd_feval [n H].
elim: n c s1 l1 st H => //=.
move => n IH [|e|e|x e|c1 c2|b c1 c2|b c] s1 l1 st H; try discriminate H.
- by move: H; case: (ifP _).
- move: H; case: (ifP _) => H //.
  move => _; exists [::]; constructor; constructor.
  move: H; rewrite /isTrue_expr eval_expr_join_i1.
  by move=> H; apply/negPf.
- move: H.
  move: {2 3}(feval_cmd lspec n c1 s1)
        (Logic.eq_refl (feval_cmd lspec n c1 s1)) => [[[s'|] l']|] E1 //.
   move: {2 3}(feval_cmd lspec n c2 s')
         (Logic.eq_refl (feval_cmd lspec n c2 s')) => [[[s''|] l'']|] E2 //.
   by admit.
  move=> [El']; move: E1; rewrite El' {El'} => E1 /=.
  elim (IH _ _ _ st E1) => ll; exists ll.
  by apply eval_SeqN.
- move: H; case: (ifP _) => Eb.
   move: {2 3}(feval_cmd lspec n c1 s1)
         (Logic.eq_refl (feval_cmd lspec n c1 s1)) => [[[s'|] l']|] E1 //.
   by admit.
  move: {2 3}(feval_cmd lspec n c2 s1)
        (Logic.eq_refl (feval_cmd lspec n c2 s1)) => [[[s'|] l']|] E1 //.
  by admit.
- move: H; case: (ifP _) => Eb //.
  move: {2 3}(feval_cmd lspec n (Seq c (While b c)) s1)
        (Logic.eq_refl (feval_cmd lspec n (Seq c (While b c)) s1))
        => [[[s'|] l']|] E1 //.
  by admit.
Qed.

Lemma product_preimgN: forall s c ll,
 eval_cmd lspec s (productTrf c) ll None ->
 (exists l1, eval_cmd lspec (splitState s).1.1 c l1 None)
 \/ (exists l2, eval_cmd lspec (splitState s).1.2 c l2 None).
Proof.
move=> s c l /eval_cmd_feval [n H].
elim: n c s l H => //.
move => n IH [|e|e|x e|c1 c2|b c1 c2|b c] s l H; try discriminate H.
- rewrite /= in H; move: {2 3}(feval_cmd lspec n (Assume _) s)
        (Logic.eq_refl (feval_cmd lspec n (Assume (ren_expr false e)) s)) H
        => [[[s'|] l']|] H1 //.
   move: {2 3}(feval_cmd lspec n (Assume _) s')
         (Logic.eq_refl (feval_cmd lspec n (Assume (ren_expr true e)) s'))
         => [[[s''|] l'']|] H2 // [E2].
   by move/feval_cmd_eval: H2 => /eval_cmd_AssumeI [].
  move=> [E1].
  by move/feval_cmd_eval: H1 => /eval_cmd_AssumeI [].
- rewrite /= in H; move: {2 3}(feval_cmd lspec n (Assert _) s)
        (Logic.eq_refl (feval_cmd lspec n (Assert (ren_expr false e)) s)) H
        => [[[s'|] l']|] H1 //.
   move: {2 3}(feval_cmd lspec n (Assert _) s')
         (Logic.eq_refl (feval_cmd lspec n (Assert (ren_expr true e)) s'))
         => [[[s''|] l'']|] H2 // [E2].
    move/feval_cmd_eval: H2 => /eval_cmd_AssertNI [] // Hb2 El2.
    move/feval_cmd_eval: H1 => /eval_cmd_AssertSI [] // Hb1 <- El1.
    right; exists [::]; constructor.
    by move: Hb2; rewrite /isTrue_expr {1}(joinSplitState s') eval_expr_join_i2.
   move=> [E1].
   move/feval_cmd_eval: H1 => /eval_cmd_AssertNI [] Hb1 El1.
   left; exists [::]; constructor.
   by move: Hb1; rewrite /isTrue_expr {1}(joinSplitState s) eval_expr_join_i1.
- admit.
- rewrite /= in H.
  move: {2 3}(feval_cmd lspec n _ s)
        (Logic.eq_refl (feval_cmd lspec n (productTrf c1) s)) H
        => [[[s'|] l']|] H1 //.
   move: {2 3}(feval_cmd lspec n _ s')
         (Logic.eq_refl (feval_cmd lspec n (productTrf c2) s'))
         => [[[s''|] l'']|] H2 // [E2].
   move/feval_cmd_eval: H1 => /product_complete [l1 [l2 [H11 H12 H13]]].
   move: {IH} (IH _ _ _ H2) => [[ll IH]|[ll IH]].
    by left; exists (l1++ll); apply eval_SeqS with (splitState s').1.1.
   by right; exists (l2++ll); apply eval_SeqS with (splitState s').1.2.
  move: {IH} (IH _ _ _ H1) => [[ll IH]|[ll IH]] [El].
   by left; exists ll; apply eval_SeqN.
  by right; exists ll; apply eval_SeqN.
- rewrite /= in H.
  move: {2 3}(feval_cmd lspec n _ s)
        (Logic.eq_refl (feval_cmd lspec n (assertEqLeakTest b) s)) H
        => [[[s'|] l']|] H1 //; last first.
   move => [El]; subst.
   admit (* assertEqLeak != None *).
  have ->: s' = updLValue s (@ok_lvalue ops) (eval_expr s b) (* it is NOT b *).
   admit (* invert feval_assertEqLeakTest *).
  move: {2 3}(feval_cmd lspec n _ _)
        (Logic.eq_refl (feval_cmd lspec n (If ok_expr (If (ren_expr false b) (productTrf c1) (productTrf c2))
          (Seq (selfComp lspec (If b c1 c2)) (ok_upd okSC_expr))) (updLValue s (@ok_lvalue ops) (eval_expr s b))))
        => [[[s''|] l'']|] H2 // [E2].
  move/feval_cmd_eval: H2 => /eval_cmd_IfI [ll].
  case: (ifP _) => Hok.
   (* Caso standard... *) admit.
  (* Caso SelfComp... 
    eval_cmd lspec s (selfComp lspec c) ll None -> 
    (exists l1, eval_cmd lspec (splitState s).1.1 c l1 None)
    \/ (exists l2, eval_cmd lspec (splitState s).1.2 c l2 None) *)
  admit.
- admit.
Qed.

Definition initProduct: cmd ops :=
 Assign ok_lvalue (Const 1).

Lemma initProduct_SeqI: forall st c l st',
 eval_cmd lspec st (Seq initProduct c) l st' ->
 eval_cmd lspec (updLValue st (@ok_lvalue ops) 1) c l st'.
Proof.
admit.
Qed.

Fixpoint assumeVarRestr (v: VarRestr) : cmd ops :=
 match v with
 | [::] => Skip _
 | x::xs => Seq (Assume (Equal (ren_expr false (ValOf (Var x))) (ren_expr true (ValOf (Var x))))) (assumeVarRestr xs)
 end.

Lemma assumeVarRestrP: forall v st l st',
 eval_cmd lspec st (assumeVarRestr v) l st'
 <->
 joinStateEqLow v st /\ l=[::] /\ st'=Some st.
Proof.
elim => [|x xs IH] st l st' /=.
 split.
  move=> /eval_cmd_SkipI [-> ->]; split; last by split.
  by rewrite /eqstateR.
 by move=> [_ [-> ->]]; constructor.
split.
 move=> /eval_cmd_SeqI
         [[-> H]|[s' [l1 [l2 [/eval_cmd_AssumeI [H1 [->] ->] H2 ->]]]]];
  first by inversion_clear H. 
 rewrite -> IH in H2; move: {IH} H2 => [H2 [-> ->]].
 split; last by [].
 by admit (* simples eqstateR_cons *).
move => [Hv [-> ->]].
 rewrite -/([::]++[::]); apply eval_SeqS with st.
  constructor.
  by admit (* simples eqstateR_cons *).
 rewrite IH; split; last by [].
 by admit (* simples eqstateR_cons *).
Qed.

Lemma assumeSeq_SeqI: forall v st c l st',
 eval_cmd lspec st (Seq (assumeVarRestr v) c) l st' ->
 eval_cmd lspec st c l st' /\ joinStateEqLow v st.
Proof.
move=> v st c l st' /eval_cmd_SeqI [[->]|[s' [l1 [l2 [H1 H2 ->]]]]].
 by rewrite assumeVarRestrP => [[_ [_ H2]]].
move: H1; rewrite assumeVarRestrP => [[H1 [-> [Es]]]] /=.
by move: H1; rewrite -Es {Es} => H1; split.
Qed.

Variable vIN vOUT: VarRestr.

Definition fullProduct (c: cmd ops) : cmd ops :=
 Seq (Seq (Seq initProduct (assumeVarRestr vIN))
          (productTrf c))
     (Seq (assumeVarRestr vOUT) (Assert ok_expr)).

Lemma fullProduct_imgN: forall st s1 c l1,
 eval_cmd lspec s1 c l1 None ->
 exists ll,
 eval_cmd lspec (joinState (s1,s1,st)) (fullProduct c) ll None.
Proof.
rewrite /fullProduct => st s1 c l1 H.
set st' := (updLValue (joinState (s1, s1, st)) (@ok_lvalue ops) 1).
move: (product_imgN (splitState st').2 H) => [ll Hll].
exists ((((leak_expr lspec (joinState (s1, s1, st)) (ValOf ok_lvalue)
         ++leak_expr lspec (joinState (s1, s1, st)) (Const 1))++[::])++ll)).
apply eval_SeqN.
eapply eval_SeqS.
 eapply eval_SeqS.
 constructor; first by reflexivity.
 rewrite assumeVarRestrP; split => //.
have HS: eqstate (joinState (s1, s1, (splitState st').2))
                 (updLValue (joinState (s1, s1, st)) (@ok_lvalue ops) 1).
 move => id /=; split => //.
 by move: id => [x|x|].
by move: (eval_cmd_eqstate HS Hll) => [[st2'|] [HH1 //= HH2]].
Qed.

Lemma fullProduct_sound': forall c s1 s2 l1 l2 s1' s2',
  eqstateR vIN s1 s2 ->
  eval_cmd lspec s1 c l1 (Some s1') ->
  eval_cmd lspec s2 c l2 (Some s2') ->
  eqstateR vOUT s1' s2' ->
  exists ss ll,
   eval_cmd lspec (joinState (s1, s2, trfState0)) (fullProduct c)
            ll ss
   /\ (ss <> None -> l1=l2).
Proof.
move => c s1 s2 l1 l2 s1' s2' Hin H1 H2 Hout.
move: (product_sound trfState0 H1 H2) => [st' [ll [HH1 HH2]]].
have HH: eval_cmd lspec (joinState (s1,s2,trfState0))
                  (Seq (Seq initProduct (assumeVarRestr vIN)) (productTrf c))
                  (((leak_expr lspec (joinState (s1, s2, trfState0))
                               (ValOf ok_lvalue)
                    ++leak_expr lspec (joinState (s1, s2, trfState0))
                                 (Const 1))++[::])++ll)
                  (Some (joinState (s1', s2', st'))).
 apply: eval_SeqS; last by apply HH1.
 apply eval_SeqS with (updLValue (joinState (s1,s2,trfState0)) (@ok_lvalue ops)1).
  constructor.
by [].
 rewrite assumeVarRestrP; split => //. 
case E: (isTrue_expr (joinState (s1', s2', st')) (@ok_expr ops)).
 exists (Some (joinState (s1', s2', st'))).
 exists ((((leak_expr lspec (joinState (s1, s2, trfState0)) (ValOf ok_lvalue)
         ++leak_expr lspec (joinState (s1, s2, trfState0)) (Const 1))++[::])++ll)++[::]).
 split; last first.
  by move=> _; rewrite -HH2.
 apply eval_SeqS with (joinState (s1', s2', st')); first by [].
 rewrite -/([::]++[::]); apply eval_SeqS with (joinState (s1', s2', st')).
  by rewrite assumeVarRestrP /joinStateEqLow; split.
 by constructor.
exists None.
exists ((((leak_expr lspec (joinState (s1, s2, trfState0)) (ValOf ok_lvalue)
         ++leak_expr lspec (joinState (s1, s2, trfState0)) (Const 1))++[::])++ll)++([::]++[::])).
split => //.
apply eval_SeqS with (joinState (s1', s2', st')); first by [].
apply eval_SeqS with (joinState (s1', s2', st')); last first.
 by constructor; rewrite E. 
by rewrite assumeVarRestrP.
Qed.

Theorem fullProduct_sound: forall c,
 Safe lspec (fullProduct c) ->
 leakSecure lspec vIN vOUT c.
Proof.
rewrite /leakSecure => c H s1 l1 ss1 H1.
move: ss1 H1 => [s1'|] H1; last first.
 move: (H (joinState (s1,s1,trfState0))) => H'.
 move/(fullProduct_imgN trfState0): H1 => [ll H1].
 by move: (H' _ _ H1).
exists s1'; split => // s2 s2' l2 HIN H2 HOUT.
move: {H} (H (joinState (s1,s2,trfState0))) => H.
move: (fullProduct_sound' HIN H1 H2 HOUT) => [st' [ll [HH1]]].
by move: {H} st' HH1 (H _ _ HH1) => [st'|] HH1 _ //; apply.
Qed.

Theorem fullProduct_complete: forall c,
 leakSecure lspec vIN vOUT c -> 
 Safe lspec (fullProduct c).
Proof.
rewrite /Safe /leakSecure => c H st.
move => [st'|] l H' => //.
move: H' => /eval_cmd_SeqNI [H'| [ss' [l1 [l2 [H1 H2 Hll]]]]].
 move: H'=> /eval_cmd_SeqNI [/initProduct_SeqI| [ss' [l1 [l2 [H1 H2 Hll]]]]].
  by rewrite assumeVarRestrP => [[_ [_ H']]].
 move: H1 => /eval_cmd_SeqSI [s1' [l1' [l2' [H1' H2' Hll']]]].
 move: H1' => /eval_cmd_AssignI [[H1a] H1b].
 move: H2'; rewrite assumeVarRestrP => [[H2a [H2b [H2c]]] _]; subst.
 move: H2 => /product_preimgN [[l1 H1]|[l2' H2]].
  by move: {H H1} (H _ _ _ H1) => [ss [Hss _]].
 by move: {H H2} (H _ _ _ H2) => [ss [Hss _]].
move: H1 => /eval_cmd_SeqSI [s1' [l1' [l2' [H1' H2' Hll']]]].
move: H1' => /eval_cmd_SeqSI [s1'' [l1'' [l2'' [H1'' H2'' Hll'']]]].
move: H1'' => /eval_cmd_AssignI [[H1a] H1b].
move: H2''; rewrite assumeVarRestrP => [[H2a [H2b [H2c]]] _]; subst.
move: H2 => /assumeSeq_SeqI [/eval_cmd_AssertNI [Hnok _] Hout].
move/negP: Hnok; apply.
move: {H2'} (product_complete H2') => [ll1 [ll2 [HH1 [HH2 HH]]]].
apply HH => //.
move: (H _ _ _ HH1) => [ss1' [[<-] HH1']] {ss1'}.
by apply HH1' with (splitState (updVar st 1%positive (eval_expr st (@Const ops 1)))).1.2 (splitState ss').1.2.
Qed.

