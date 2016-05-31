Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Open Scope Z_scope.

(** * Combined State

   The product construction demands fresh variables 
*)

Record trfState := mkTrfSt { ok : Z
                           ; sc: Z -> Z }.

Definition trfState0 := mkTrfSt 0 (fun _ => 0).

Definition TrfState := (State*State*trfState)%type.

Definition eqtrfstate (ssa ssb:trfState) : Prop :=
 ok ssa = ok ssb /\ forall i, sc ssa i = sc ssb i.

Lemma eqtrfstate_refl: forall ss, eqtrfstate ss ss.
Proof. rewrite /eqtrfstate; move => [s1 s2] /=; split; reflexivity. Qed.

Lemma eqtrfstate_sym: forall ss1 ss2,
 eqtrfstate ss1 ss2 -> eqtrfstate ss2 ss1.
Proof.
by rewrite /eqtrfstate; move => [s11 s12] [s21 s22] /= [-> H]; split.
Qed.

Lemma eqtrfstate_trans: forall ss1 ss2 ss3,
 eqtrfstate ss1 ss2 -> eqtrfstate ss2 ss3 -> eqtrfstate ss1 ss3.
Proof.
rewrite /eqtrfstate.
move => [s11 s12] [s21 s22] [s31 s32] /= [-> H1] [-> H2]; split => //.
by move => i; rewrite (H1 i).
Qed.

Add Parametric Relation : (trfState) eqtrfstate
 reflexivity proved by eqtrfstate_refl
 symmetry proved by eqtrfstate_sym
 transitivity proved by eqtrfstate_trans
 as eqtrfstate_equiv.

Definition eqstatePair (ssa ssb:State*State) : Prop :=
 eqstate ssa.1 ssb.1 /\ eqstate ssa.2 ssb.2.

Lemma eqstatePair_refl: forall ss, eqstatePair ss ss.
Proof. rewrite /eqstatePair; move => [s1 s2] /=; split; reflexivity. Qed.

Lemma eqstatePair_sym: forall ss1 ss2,
 eqstatePair ss1 ss2 -> eqstatePair ss2 ss1.
Proof.
by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [-> ->]; split.
Qed.

Lemma eqstatePair_trans: forall ss1 ss2 ss3,
 eqstatePair ss1 ss2 -> eqstatePair ss2 ss3 -> eqstatePair ss1 ss3.
Proof.
rewrite /eqstatePair.
by move => [s11 s12] [s21 s22] [s31 s32] /= [-> ->] [-> ->]; split.
Qed.

Add Parametric Relation : (State*State) eqstatePair
 reflexivity proved by eqstatePair_refl
 symmetry proved by eqstatePair_sym
 transitivity proved by eqstatePair_trans
 as eqstatePair_equiv.

Definition eqTrfState (ssa ssb:TrfState) : Prop :=
 eqstatePair ssa.1 ssb.1 /\ eqtrfstate ssa.2 ssb.2.

Lemma eqTrfState_refl: forall ss, eqTrfState ss ss.
Proof. by rewrite /eqTrfState; move => [s1 s2] /=; split. Qed.

Lemma eqTrfState_sym: forall ss1 ss2,
 eqTrfState ss1 ss2 -> eqTrfState ss2 ss1.
Proof.
rewrite /eqTrfState; move => [s11 s12] [s21 s22] /= [H1 H2]; split.
 by apply eqstatePair_sym.
by apply eqtrfstate_sym.
Qed.

Lemma eqTrfState_trans: forall ss1 ss2 ss3,
 eqTrfState ss1 ss2 -> eqTrfState ss2 ss3 -> eqTrfState ss1 ss3.
Proof.
rewrite /eqTrfState.
move => [[s11 s12] s13] [[s21 s22] s23] [[s31 s32] s33] /=.
move => [H11 H12] [H21 H22]; split.
 by eapply eqstatePair_trans; eauto.
by eapply eqtrfstate_trans; eauto.
Qed.

Add Parametric Relation : (TrfState) eqTrfState
 reflexivity proved by eqTrfState_refl
 symmetry proved by eqTrfState_sym
 transitivity proved by eqTrfState_trans
 as eqTrfState_equiv.

Add Parametric Morphism : (@fst State State)
 with signature eqstatePair ==> eqstate
 as fstState_morph.
Proof. by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [-> _]. Qed.

Add Parametric Morphism : (@snd State State)
 with signature eqstatePair ==> eqstate
 as sndState_morph.
Proof. 
by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [_ ->].
Qed.

Add Parametric Morphism : (@pair State State)
 with signature eqstate ==> eqstate ==> eqstatePair
 as pairState_morph.
Proof. by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /=. Qed.

Add Parametric Morphism : (@fst (State*State) trfState)
 with signature eqTrfState ==> eqstatePair
 as fstTrfState_morph.
Proof. 
by rewrite /eqTrfState; move => [s11 s12] [s21 s22] /= [-> _].
Qed.

Add Parametric Morphism : (@snd (State*State) trfState)
 with signature eqTrfState ==> eqtrfstate
 as sndTrfState_morph.
Proof. 
by rewrite /eqTrfState; move => [s11 s12] [s21 s22] /= [_ H].
Qed.

Add Parametric Morphism : (@pair (State*State) trfState)
 with signature eqstatePair ==> eqtrfstate ==> eqTrfState
 as pairTrfState_morph.
Proof. by rewrite /eqTrfState; move => [s11 s12] [s21 s22] /=. Qed.

Section StateJoin.

Definition idA (f:ident->ident) (i:ident*Z) : ident*Z := (f i.1, i.2).

(** a bijection between [Z+Z] and [Z]                     *)
Definition id_i1 x := xO x.
Definition id_i2 x := xI x.

Lemma id_i1_Nodd: forall x y, xI x == id_i1 y = false.
Proof. move => x y; apply/negP => /eqP H; discriminate H. Qed.

Lemma id_i2_Neven: forall x y, xO x == id_i2 y = false.
Proof. move => x [y|y|]; apply/negP => /eqP H; discriminate H. Qed.

Definition id_sel x (f1 f2:ident -> Z) (i:ident) : Z :=
 match i with
 | xO i' => f1 i'
 | xI i' => f2 i'
 | xH => x
 end.
Definition id_selA fx (f1 f2:ident*Z -> Z) (i:ident*Z) : Z :=
 match i.1 with
 | xO i' => f1 (i',i.2)
 | xI i' => f2 (i',i.2)
 | xH => fx i.2
 end.

(*
Lemma id_sel_i2: forall z (f1 f2:ident -> Z) (x:ident),
 id_sel z f1 f2 (id_i2 x) = f2 x.
Proof. by []. Qed.

Lemma id_selA_i2: forall f1 f2 x z,
 id_selA f1 f2 (id_i2 x,z) = f2 (x,z).
Proof.
move => f1 f2 [x|x|] //= z.
by rewrite /id_selA /= Pos.succ_pred_double.
Qed.
*)

Definition joinState (st: TrfState) : State :=
 (id_sel (ok st.2) st.1.1.1 st.1.2.1, id_selA (sc st.2) st.1.1.2 st.1.2.2).

Definition splitState (s:State) : TrfState :=
 ( (fun i => s.1 (id_i1 i), fun ai => s.2 (idA id_i1 ai))
 , (fun i => s.1 (id_i2 i), fun ai => s.2 (idA id_i2 ai))
 , mkTrfSt (s.1 xH) (fun i=>s.2 (xH,i)) ).

Lemma split_joinState_1: forall (st1 st2:State) (ts:trfState),
 eqstate (splitState (joinState (st1,st2,ts))).1.1 st1.
Proof. by []. Qed.

Lemma split_joinState_2: forall (st1 st2:State) (ts:trfState),
 eqstate (splitState (joinState (st1,st2,ts))).1.2 st2.
Proof. by []. Qed.

Lemma join_splitState: forall st,
 eqstate (joinState (splitState st)) st.
Proof. move => st [i|i|] => //=. Qed.

Definition joinStateEqLow (lowMap:VarRestr) (s:State) : Prop :=
 eqstateR lowMap (splitState s).1.1 (splitState s).1.2.

Lemma joinState_compat: forall s s',
 eqTrfState s s' -> eqstate (joinState s) (joinState s').
Proof.
rewrite /eqTrfState /eqstatePair => [[[s1 s2] s] [[s1' s2'] s']] /=. 
move => [[Es1 Es2] Es] [x|x|] /=.
  by move: {Es2} (Es2 x) => [Es21 Es22]; split.
 by move: {Es1 Es2} (Es1 x) => [Es11 Es12]; split.
move: {Es1 Es2} Es => [/eqP Es1 Es2]; split => //=.
by move => x; rewrite /id_selA (Es2 x).
Qed.
(*
Lemma joinState_compat: forall s s',
 eqtrfstate s s' -> forall st1 st1', 
 eqstate st1 st1' -> forall st2 st2',
 eqstate st2 st2' -> eqstate (joinState (st1,st2,s)) (joinState (st1',st2',s')).
Proof.
move => s s' Es st1 st1' EqS1 st2 st2' EqS2 [x|x|] /=.
  by move: {EqS2} (EqS2 x) => [Es21 Es22]; split.
 by move: {EqS1} (EqS1 x) => [Es11 Es12]; split.
move: Es => [/eqP Es1 Es2]; split => //=.
by move => x; rewrite /id_selA (Es2 x).
Qed.
*)
Lemma splitState_compat1: forall st st', 
 eqstate st st' -> eqstate (splitState st).1.1 (splitState st').1.1.
Proof.
rewrite /splitState => st st' EqS i /=.
by move: {EqS} (EqS (id_i1 i)) => [H1 H2]; split.
Qed.

Lemma splitState_compat2: forall st st', 
 eqstate st st' -> eqstate (splitState st).1.2 (splitState st').1.2.
Proof.
rewrite /splitState => st st' EqS i /=.
by move: {EqS} (EqS (id_i2 i)) => [H1 H2]; split.
Qed.

Lemma splitState_compat3: forall st st', 
 eqstate st st' -> eqtrfstate (splitState st).2 (splitState st').2.
Proof.
rewrite /splitState /eqtrfstate => st st' EqS /=.
move: {EqS} (EqS xH) => [/eqP H1 H2]; split => // i.
by move: (H2 i) => /eqP ->.
Qed.

Lemma joinSplitState: forall s,
 eqstate s
         (joinState ((splitState s).1.1,(splitState s).1.2,(splitState s).2)).
Proof.
move=> s.
have ->: ((splitState s).1.1, (splitState s).1.2, (splitState s).2)
         = splitState s.
 by case: (splitState s) => [[s11 s12] s2].
by rewrite join_splitState.
Qed.

Variable ops: opSig.

Fixpoint ren_expr side (e: expr ops) : expr ops :=
 match e with
 | ValOf l => ValOf (ren_lvalue side l)
 | Const z => @Const ops z
 | Minus e1 e2 => Minus (ren_expr side e1) (ren_expr side e2)
 | Mult e1 e2 => Mult (ren_expr side e1) (ren_expr side e2)
 | Equal e1 e2 => Equal (ren_expr side e1) (ren_expr side e2)
 | Op o args => @Op ops _ (@ren_texpr side (op_arity o) args)
 end
with ren_texpr side {n:nat} (x:texpr ops n) : texpr ops n :=
 match x with
 | t_nil => @t_nil ops
 | t_cons _ x l => t_cons (ren_expr side x) (ren_texpr side l)
 end
with ren_lvalue side l :=
 match l with
 | Var v => @Var _ (if side then xI v else xO v)
 | ArrCell a e => ArrCell (if side then xI a else xO a) (ren_expr side e)
 end.

Lemma ren_Minus: forall f (e1 e2:expr ops),
 ren_expr f (Minus e1 e2) = Minus (ren_expr f e1) (ren_expr f e2).
Proof. by []. Qed.

Lemma ren_Mult: forall f (e1 e2:expr ops),
 ren_expr f (Mult e1 e2) = Mult (ren_expr f e1) (ren_expr f e2).
Proof. by []. Qed.

Lemma ren_Equal: forall f (e1 e2:expr ops),
 ren_expr f (Equal e1 e2) = Equal (ren_expr f e1) (ren_expr f e2).
Proof. by []. Qed.

Lemma ren_tcons: forall f (e:expr ops) n (t:texpr ops n),
 ren_texpr f (t_cons e t) = t_cons (ren_expr f e) (ren_texpr f t).
Proof. by []. Qed.

Lemma ren_ArrCell: forall f a (e:expr ops),
 ren_lvalue f (ArrCell a e) = ArrCell (if f then xI a else xO a) (ren_expr f e).
Proof. by []. Qed.

Definition expr_i1 e := ren_expr false e.
Definition expr_i2 e := ren_expr true e.
Definition lvalue_i1 e := ren_lvalue false e.
Definition lvalue_i2 e := ren_lvalue true e.

Lemma eval_expr_join_i1: forall e s st1 st2,
 eval_expr (joinState (st1,st2,s)) (expr_i1 e) = eval_expr st1 e.
Proof.
pose P1 e := (forall s (st1 st2 : State),
 eval_expr (joinState (st1,st2,s)) (ren_expr false e) = eval_expr st1 e).
pose P2 n (args: texpr ops n) := (forall s (st1 st2 : State) zl,
 eval_texpr (joinState (st1,st2,s)) zl (ren_texpr false args)
 = eval_texpr st1 zl args).
pose P3 l := (forall s (st1 st2 : State),
 eval_lvalue (joinState (st1,st2,s)) (ren_lvalue false l) = eval_lvalue st1 l).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3.
(* ValOf *) 
move => l IH s st1 st2.
by apply IH.
(* Const *)
by move => z s st1 st2 /=.
(* Minus *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Minus e1 e2) = eval_expr st e1 - eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Mult *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Mult e1 e2) = eval_expr st e1 * eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Equal *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Equal e1 e2) 
         = (if eval_expr st e1 == eval_expr st e2 then 1 else 0) by [].
by rewrite IH1 IH2.
(* Op *)
move => o args IH s st1 st2 /=.
have ->: forall st (args:texpr ops (op_arity o)),
         eval_expr st (Op args)
         = op_sem o (eval_texpr st [::] args) by []. 
by rewrite IH.
(* t_nil *)
by move => s st1 st2.
(* t_cons *)
move => n e IHe args IHargs s st1 st2 zl /=.
have E: forall st zl n e (args:texpr ops n),
         eval_texpr st zl (t_cons e args)
         = eval_texpr st [:: eval_expr st e & zl] args by [].
by rewrite !E IHe IHargs.
(* Var *)
move => v s st1 st2 /=.
have E: forall st v,
         eval_lvalue st (Var v)
         = st.1 v by [].
by rewrite !E.
(* ArrCell *)
move => a i IHi s st1 st2 /=.
have E: forall st a e,
         eval_lvalue st (ArrCell a e)
         = st.2 (a,eval_expr st e) by [].
by rewrite !E /= /id_selA /= IHi.
Qed.

Lemma eval_expr_join_i2: forall e s st1 st2,
 eval_expr (joinState (st1,st2,s)) (expr_i2 e) = eval_expr st2 e.
Proof.
pose P1 e := (forall s (st1 st2 : State),
 eval_expr (joinState (st1,st2,s)) (ren_expr true e) = eval_expr st2 e).
pose P2 n (args: texpr ops n) := (forall s (st1 st2 : State) zl,
 eval_texpr (joinState (st1,st2,s)) zl (ren_texpr true args)
 = eval_texpr st2 zl args).
pose P3 l := (forall s (st1 st2 : State),
 eval_lvalue (joinState (st1,st2,s)) (ren_lvalue true l) = eval_lvalue st2 l).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3.
(* ValOf *)
move => l IH s st1 st2.
by apply IH.
(* Const *)
by move => z s st1 st2 /=.
(* Minus *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Minus e1 e2) = eval_expr st e1 - eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Mult *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Mult e1 e2) = eval_expr st e1 * eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Equal *)
move => e1 IH1 e2 IH2 s st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Equal e1 e2) 
         = (if eval_expr st e1 == eval_expr st e2 then 1 else 0) by [].
by rewrite IH1 IH2.
(* Op *)
move => o args IH s st1 st2 /=.
have ->: forall st (args:texpr ops (op_arity o)),
         eval_expr st (Op args)
         = op_sem o (eval_texpr st [::] args) by []. 
by rewrite IH.
(* t_nil *)
by move => s st1 st2.
(* t_cons *)
move => n e IHe args IHargs s st1 st2 zl /=.
have E: forall st zl n e (args:texpr ops n),
         eval_texpr st zl (t_cons e args)
         = eval_texpr st [:: eval_expr st e & zl] args by [].
by rewrite !E IHe IHargs.
(* Var *)
move => v s st1 st2 /=.
have E: forall st v,
         eval_lvalue st (Var v)
         = st.1 v by [].
by rewrite !E.
(* ArrCell *)
move => a i IHi s st1 st2 /=.
have E: forall st a e,
         eval_lvalue st (ArrCell a e)
         = st.2 (a,eval_expr st e) by [].
by rewrite !E /= IHi /=.
Qed.

Lemma updLValue_join_i1: forall s st1 st2 x y,
 eqstate (updLValue (joinState (st1,st2,s)) (lvalue_i1 x) y)
         (joinState (updLValue st1 x y,st2,s)).
Proof.
move => s st1 st2 [v|a e] y x /=; rewrite /upd; split => //=.
 move: x => [x|x|] //=.
 by rewrite id_i1_Nodd.
move: x => [x|x|] z; rewrite /id_selA xpair_eqE ?id_i1_Nodd //=.
by rewrite xpair_eqE /id_i1 eval_expr_join_i1.
Qed.

Lemma updLValue_join_i2: forall s st1 st2 x y,
 eqstate (updLValue (joinState (st1,st2,s)) (lvalue_i2 x) y)
         (joinState (st1,updLValue st2 x y,s)).
Proof.
move => s st1 st2 [v|a e] y x /=; rewrite /upd; split => //=.
 move: x => [x|x|] //=.
 by rewrite id_i2_Neven.
move: x => [x|x|] z; rewrite /id_selA xpair_eqE ?id_i2_Neven //=.
by rewrite xpair_eqE /id_i2 eval_expr_join_i2.
Qed.

Lemma eval_updLValue_i1: forall s st1 st2 x y e,
 eval_expr (updLValue (joinState (st1,st2,s)) (lvalue_i1 x) y) (expr_i2 e)
 = eval_expr (joinState (st1,st2,s)) (expr_i2 e).
Proof. 
by move=> s st1 st2 x y e; rewrite updLValue_join_i1 !eval_expr_join_i2.
Qed.

End StateJoin.

Add Parametric Morphism : joinState
 with signature eqTrfState ==> eqstate
 as joinState_morph.
Proof. by intro; apply joinState_compat. Qed.

Add Parametric Morphism : splitState
 with signature eqstate ==> eqTrfState
 as splitState_morph.
Proof.
rewrite /eqTrfState /eqstatePair => s1 s2 EqS.
by rewrite splitState_compat1 // splitState_compat2 // splitState_compat3.
Qed.

