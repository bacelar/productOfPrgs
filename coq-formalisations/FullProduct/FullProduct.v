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

   The product construction demands ...
*)
Section StateJoin.

Definition idA (f:ident->ident) (i:ident*Z) : ident*Z := (f i.1, i.2).

Definition id_i1 x := xO x.

Lemma id_i1_Nodd: forall x y, xI x == id_i1 y = false.
Proof. move => x y; apply/negP => /eqP H; discriminate H. Qed.

Definition id_i2 x := xI x.

Lemma id_i2_Neven: forall x y, xO x == id_i2 y = false.
Proof. move => x [y|y|]; apply/negP => /eqP H; discriminate H. Qed.

Definition idA_i2 x :=
 match x with
 | xI p => xI (xO p)
 | xO p => xI (Pos.pred x)
 | xH => xH
 end.

Lemma idA_i2_Neven: forall x y, xO x == id_i2 y = false.
Proof. move => x [y|y|]; apply/negP => /eqP H; discriminate H. Qed.

Lemma idA_i2_sel: forall x,
 idA_i2 (Pos.succ x) = xI x.
Proof. by move => [x|x|] //=; rewrite Pos.pred_double_succ. Qed.

Definition id_sel (f1 f2:ident -> Z) (b:Z) (i:ident) : Z :=
 match i with
 | xO i' => f1 i'
 | xI i' => f2 i'
 | xH => b
 end.

Definition id_selA (f1 f2:ident*Z -> Z) (i:ident*Z) : Z :=
 match i.1 with
 | xO i' => f1 (i',i.2)
 | xI i' => f2 (Pos.succ i',i.2)
 | xH => f2 (xH, i.2)
 end.
(*
Lemma idA_sel_i2: forall (f1 f2:ident -> Z) b (x:ident),
 id_sel f1 f2 b (idA_i2 x) = f2 x.
Proof. 
move => f1 f2 [x|x|] //=.
by rewrite Pos.succ_pred_double.
Qed.
*)
Lemma id_selA_i2: forall f1 f2 x z,
 id_selA f1 f2 (idA_i2 x,z) = f2 (x,z).
Proof.
move => f1 f2 [x|x|] //= z.
by rewrite /id_selA /= Pos.succ_pred_double.
Qed.

Definition joinState (s1 s2:State) (b:Z) : State :=
 (id_sel s1.1 s2.1 b, id_selA s1.2 s2.2).

Definition splitState (s:State) : State*State*Z :=
 ( (fun i => s.1 (id_i1 i), fun ai => s.2 (idA id_i1 ai))
 , (fun i => s.1 (id_i2 i), fun ai => s.2 (idA idA_i2 ai))
 , s.1 xH).

Lemma split_joinState_1: forall st1 st2 b,
 eqstate (splitState (joinState st1 st2 b)).1.1 st1.
Proof. by []. Qed.

Lemma split_joinState_2: forall st1 st2 b,
 eqstate (splitState (joinState st1 st2 b)).1.2 st2.
Proof. 
rewrite /splitState /joinState => st1 st2 b x /=; split => //.
by move => i; rewrite id_selA_i2.
Qed.

Lemma split_joinState_3: forall st1 st2 b,
 (splitState (joinState st1 st2 b)).2 = b.
Proof. by []. Qed.

Lemma join_splitState: forall st,
 eqstate
   (joinState (splitState st).1.1 (splitState st).1.2 (splitState st).2)
   st.
Proof. 
move => st [i|i|]; rewrite /joinState /splitState /idA //=; split; first by [].
by rewrite /id_selA //= idA_i2_sel.
Qed.

Definition joinStateEqLow (lowMap:VarRestr) (s:State) : Prop :=
 eqstateR lowMap (splitState s).1.1 (splitState s).1.2.

Lemma joinState_compat: forall st1 st1' b, 
 eqstate st1 st1' -> forall st2 st2',
 eqstate st2 st2' -> eqstate (joinState st1 st2 b) (joinState st1' st2' b).
Proof.
rewrite /joinState => st1 st1' b EqS1 st2 st2' EqS2 [x|x|];
rewrite /id_sel /id_selA //=; split => //.
  by move: (EqS2 x) => [? ?].
 by move: (EqS2 (Pos.succ x)) => [? ?].
by move: (EqS2 (1%positive)) => [? ?].
Qed.

Lemma splitState_compat1: forall st st', 
 eqstate st st' -> eqstate (splitState st).1.1 (splitState st').1.1.
Proof.
rewrite /splitState => st st' EqS i /=.
by move: {EqS} (EqS (id_i1 i)) => [H1 H2]; split.
Qed.

Lemma splitState_compat2: forall st st', 
 eqstate st st' -> eqstate (splitState st).1.2 (splitState st').1.2.
Proof.
rewrite /splitState => st st' EqS i /=; split.
 by move: {EqS} (EqS (id_i2 i)) => [H1 H2].
by move: {EqS} (EqS (idA_i2 i)) => [H1 H2].
Qed.

Lemma splitState_compat3: forall st st',
 eqstate st st' -> (splitState st).2 = (splitState st').2.
Proof.
rewrite /splitState => st st' EqS /=.
by move: {EqS} (EqS (1%positive)) => [/eqP -> _].
Qed.

Variable ops: opSig.

Fixpoint ren_expr f fA (e: expr ops) : expr ops :=
 match e with
 | ValOf l => ValOf (ren_lvalue f fA l)
 | Const z => @Const ops z
 | Minus e1 e2 => Minus (ren_expr f fA e1) (ren_expr f fA e2)
 | Mult e1 e2 => Mult (ren_expr f fA e1) (ren_expr f fA e2)
 | Equal e1 e2 => Equal (ren_expr f fA e1) (ren_expr f fA e2)
 | Op o args => @Op ops _ (@ren_texpr f fA (op_arity o) args)
 end
with ren_texpr f fA {n:nat} (x:texpr ops n) : texpr ops n :=
 match x with
 | t_nil => @t_nil ops
 | t_cons _ x l => t_cons (ren_expr f fA x) (ren_texpr f fA l)
 end
with ren_lvalue f fA l :=
 match l with
 | Var v => @Var _ (f v)
 | ArrCell a e => ArrCell (fA a) (ren_expr f fA e)
 end.

Lemma ren_Minus: forall f fA (e1 e2:expr ops),
 ren_expr f fA (Minus e1 e2) = Minus (ren_expr f fA e1) (ren_expr f fA e2).
Proof. by []. Qed.

Lemma ren_Mult: forall f fA (e1 e2:expr ops),
 ren_expr f fA (Mult e1 e2) = Mult (ren_expr f fA e1) (ren_expr f fA e2).
Proof. by []. Qed.

Lemma ren_Equal: forall f fA (e1 e2:expr ops),
 ren_expr f fA (Equal e1 e2) = Equal (ren_expr f fA e1) (ren_expr f fA e2).
Proof. by []. Qed.

Lemma ren_tcons: forall f fA (e:expr ops) n (t:texpr ops n),
 ren_texpr f fA (t_cons e t) = t_cons (ren_expr f fA e) (ren_texpr f fA t).
Proof. by []. Qed.

Lemma ren_ArrCell: forall f fA a (e:expr ops),
 ren_lvalue f fA (ArrCell a e) = ArrCell (fA a) (ren_expr f fA e).
Proof. by []. Qed.

Definition expr_i1 e := ren_expr id_i1 id_i1 e.
Definition expr_i2 e := ren_expr id_i2 idA_i2 e.
Definition texpr_i1 {n} (l:texpr ops n) := ren_texpr id_i1 id_i1 l.
Definition texpr_i2 {n} (l:texpr ops n) := ren_texpr id_i2 idA_i2 l.
Definition lvalue_i1 e := ren_lvalue id_i1 id_i1 e.
Definition lvalue_i2 e := ren_lvalue id_i2 idA_i2 e.

Lemma eval_expr_join_i1: forall e st1 st2 b,
 eval_expr (joinState st1 st2 b) (expr_i1 e) = eval_expr st1 e.
Proof.
pose P1 e := (forall st1 st2 b,
 eval_expr (joinState st1 st2 b) (expr_i1 e) = eval_expr st1 e).
pose P2 n (args: texpr ops n) := (forall st1 st2 b zl,
 eval_texpr (joinState st1 st2 b) zl (texpr_i1 args)
 = eval_texpr st1 zl args).
pose P3 l := (forall st1 st2 b,
 eval_lvalue (joinState st1 st2 b) (lvalue_i1 l) = eval_lvalue st1 l).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3.
(* ValOf *) 
move => l IH st1 st2 b.
by apply IH.
(* Const *)
by move => z st1 st2 b /=.
(* Minus *)
move => e1 IH1 e2 IH2 st1 st2 b /=.
rewrite /expr_i1 ren_Minus eval_Minus.
by rewrite -/(expr_i1 e1) -/(expr_i1 e2) IH1 IH2.
(* Mult *)
move => e1 IH1 e2 IH2 st1 st2 b /=.
rewrite /expr_i1 ren_Mult eval_Mult.
by rewrite -/(expr_i1 e1) -/(expr_i1 e2) IH1 IH2.
(* Equal *)
move => e1 IH1 e2 IH2 st1 st2 b /=.
rewrite /expr_i1 ren_Equal eval_Equal.
by rewrite -/(expr_i1 e1) -/(expr_i1 e2) IH1 IH2.
(* Op *)
move => o args IH st1 st2 b /=.
Admitted.
(*
have ->: forall st (args:texpr ops (op_arity o)),
         eval_expr st (Op args)
         = op_sem o (eval_texpr st [::] args) by []. 
by rewrite IH.
(* t_nil *)
by move => st1 st2.
(* t_cons *)
move => n e IHe args IHargs st1 st2 zl /=.
have E: forall st zl n e (args:texpr ops n),
         eval_texpr st zl (t_cons e args)
         = eval_texpr st [:: eval_expr st e & zl] args by [].
by rewrite !E IHe IHargs.
(* Var *)
move => v st1 st2 /=.
have E: forall st v,
         eval_lvalue st (Var ops v)
         = st.1 v by [].
by rewrite !E.
(* ArrCell *)
move => a i IHi st1 st2 /=.
have E: forall st a e,
         eval_lvalue st (ArrCell a e)
         = st.2 (a,eval_expr st e) by [].
by rewrite !E /= /id_selA /= IHi.
Qed.
*)

Lemma eval_expr_join_i2: forall e st1 st2 b,
 eval_expr (joinState st1 st2 b) (expr_i2 e) = eval_expr st2 e.
Proof.
Admitted.
(*
pose P1 e := (forall st1 st2 : State,
 eval_expr (joinState st1 st2) (ren_expr id_i2 e) = eval_expr st2 e).
pose P2 n (args: texpr ops n) := (forall (st1 st2 : State) zl,
 eval_texpr (joinState st1 st2) zl (ren_texpr id_i2 args)
 = eval_texpr st2 zl args).
pose P3 l := (forall st1 st2 : State,
 eval_lvalue (joinState st1 st2) (ren_lvalue id_i2 l) = eval_lvalue st2 l).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3.
(* ValOf *)
move => l IH st1 st2.
by apply IH.
(* Const *)
by move => z st1 st2 /=.
(* Minus *)
move => e1 IH1 e2 IH2 st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Minus e1 e2) = eval_expr st e1 - eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Mult *)
move => e1 IH1 e2 IH2 st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Mult e1 e2) = eval_expr st e1 * eval_expr st e2 by [].
by rewrite IH1 IH2.
(* Equal *)
move => e1 IH1 e2 IH2 st1 st2 /=.
have ->: forall st e1 e2,
         eval_expr st (Equal e1 e2) 
         = (if eval_expr st e1 == eval_expr st e2 then 1 else 0) by [].
by rewrite IH1 IH2.
(* Op *)
move => o args IH st1 st2 /=.
have ->: forall st (args:texpr ops (op_arity o)),
         eval_expr st (Op args)
         = op_sem o (eval_texpr st [::] args) by []. 
by rewrite IH.
(* t_nil *)
by move => st1 st2.
(* t_cons *)
move => n e IHe args IHargs st1 st2 zl /=.
have E: forall st zl n e (args:texpr ops n),
         eval_texpr st zl (t_cons e args)
         = eval_texpr st [:: eval_expr st e & zl] args by [].
by rewrite !E IHe IHargs.
(* Var *)
move => v st1 st2 /=.
have E: forall st v,
         eval_lvalue st (Var ops v)
         = st.1 v by [].
by rewrite !E /= id_sel_i2.
(* ArrCell *)
move => a i IHi st1 st2 /=.
have E: forall st a e,
         eval_lvalue st (ArrCell a e)
         = st.2 (a,eval_expr st e) by [].
by rewrite !E /= IHi id_selA_i2 /=.
Qed.
*)

Lemma updLValue_join_i1: forall st1 st2 b x y,
 eqstate (updLValue (joinState st1 st2 b) (lvalue_i1 x) y)
         (joinState (updLValue st1 x y) st2 b).
Proof.
Admitted.
(*
move => st1 st2 [v|a e] y x /=; rewrite /upd; split => //=.
 move: x => [x|x|] //=.
 by rewrite id_i1_Nodd.
move: x => [x|x|] z; rewrite /id_selA xpair_eqE ?id_i1_Nodd //=.
by rewrite xpair_eqE /id_i1 eval_expr_join_i1.
Qed.
*)

Lemma updLValue_join_i2: forall st1 st2 b x y,
 eqstate (updLValue (joinState st1 st2 b) (lvalue_i2 x) y)
         (joinState st1 (updLValue st2 x y) b).
Proof.
Admitted.
(*
have P: forall x y, Pos.succ x == y = (xI x == id_i2 y).
 move => x y; case E: (y==Pos.succ x).
  rewrite (eqP E) eq_refl /id_i2 /= ; destruct x => //=.
   by rewrite Pos.pred_double_succ eq_refl.
  by rewrite eq_refl.
 rewrite eq_sym in E; rewrite E /id_i2; symmetry; apply/negP => /eqP HH.
 move/negP: E; apply; apply/eqP.
 destruct y; rewrite //= in HH; injection HH => -> //=.
 by rewrite Pos.succ_pred_double.
move => st1 st2 [v|a e] y x /=; rewrite /upd; split => //=.
 move: x => [x|x|] //=.
   by rewrite P.
  by rewrite id_i2_Neven.
 by destruct v.
move: x => [x|x|] z;
rewrite /id_selA xpair_eqE ?id_i2_Neven //= xpair_eqE eval_expr_join_i2.
 by rewrite P.
by destruct a.
Qed.

Lemma eval_updLValue_i1: forall st1 st2 x y e,
 eval_expr (updLValue (joinState st1 st2) (lvalue_i1 x) y) (expr_i2 e)
 = eval_expr (joinState st1 st2) (expr_i2 e).
Proof.
by move=> st1 st2 x y e; rewrite updLValue_join_i1 !eval_expr_join_i2.
Qed.
*)

End StateJoin.

Add Parametric Morphism : joinState
 with signature eqstate ==> eqstate ==> @eq Z ==> eqstate
 as joinState_morph.
Proof. by intros; apply joinState_compat. Qed.

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

Definition eqstateTriple (ssa ssb:State*State*Z) : Prop :=
 eqstate ssa.1.1 ssb.1.1 /\ eqstate ssa.1.2 ssb.1.2 /\ ssa.2 = ssb.2.

Lemma eqstateTriple_refl: forall ss, eqstateTriple ss ss.
Proof. by rewrite /eqstateTriple; move => [s1 s2] /=; split. Qed.

Lemma eqstateTriple_sym: forall ss1 ss2,
 eqstateTriple ss1 ss2 -> eqstateTriple ss2 ss1.
Proof.
Admitted.
(*
by rewrite /eqstateTriple; move => [s11 s12] [s21 s22] /= [-> ->]; split.
Qed.
*)

Lemma eqstateTriple_trans: forall ss1 ss2 ss3,
 eqstateTriple ss1 ss2 -> eqstateTriple ss2 ss3 -> eqstateTriple ss1 ss3.
Proof.
rewrite /eqstateTriple.
Admitted.
(*
by move => [s11 s12] [s21 s22] [s31 s32] /= [-> ->] [-> ->]; split.
Qed.
*)

Add Parametric Relation : (State*State*Z) eqstateTriple
 reflexivity proved by eqstateTriple_refl
 symmetry proved by eqstateTriple_sym
 transitivity proved by eqstateTriple_trans
 as eqstateTriple_equiv.

Add Parametric Morphism : splitState
 with signature eqstate ==> eqstateTriple
 as splitState_morph.
Proof.
rewrite /eqstateTriple => s1 s2 EqS.
 rewrite splitState_compat1 // splitState_compat2 //.
rewrite (@splitState_compat3 _ s2) //.
Qed.

Add Parametric Morphism : (@fst (State*State) Z)
 with signature eqstateTriple ==> eqstatePair
 as fstStateTriple_morph.
Proof. 
Admitted.
(*
 rewrite /eqstateTriple; move => [s11 s12] [s21 s22] /= [-> _].
Qed.
*)

Add Parametric Morphism : (@snd (State*State) Z)
 with signature eqstateTriple ==> @eq Z
 as sndStateTriple_morph.
Proof. 
Admitted.
(*
by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [_ ->].
Qed.
*)

Add Parametric Morphism : (@fst State State)
 with signature eqstatePair ==> eqstate
 as fstState_morph.
Proof. 
by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [-> _].
Qed.

Add Parametric Morphism : (@snd State State)
 with signature eqstatePair ==> eqstate
 as sndState_morph.
Proof. 
by rewrite /eqstatePair; move => [s11 s12] [s21 s22] /= [_ ->].
Qed.

Section ProdTrf.

Variable ops: opSig.

(** * Leakage-specification:


*)
Record LeakSpec :=
 { lFun :> @LeakFun ops
 ; preleak: expr ops -> seq (expr ops)
 ; preleak_ren: forall f fA e,
     preleak (ren_expr f fA e) = map (ren_expr f fA) (preleak e)
 ; preleak_prod: forall s1 s2 e,
     (leak_expr preleak s1 e == leak_expr preleak s2 e)
     = (leak_expr lFun s1 e == leak_expr lFun s2 e)
 }.

Variable lspec: LeakSpec.

Definition EqLeak (e1 e2: expr ops): expr ops :=
 EqSeqExpr (preleak lspec e1) (preleak lspec e2).

(*
Lemma isTrue_EqLeak: forall st1 st2 b e,
 isTrue_expr (joinState st1 st2 b) (EqLeak (expr_i1 e) (expr_i2 e))
 <-> leak_expr (preleak lspec) st1 e = leak_expr (preleak lspec) st2 e.
Proof.
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
Qed.
*)

Definition assertEqLeakTest (e1 e2: expr ops): cmd ops :=
 Assert (And (Equal (IsTrue e1) (IsTrue e2))
             (EqLeak e1 e2)).

Parameter Or : expr ops -> expr ops -> expr ops.
Parameter check : expr ops -> cmd ops.
Parameter checkTest : expr ops -> expr ops -> cmd ops.
Parameter cmd_i1 : cmd ops -> cmd ops.
Parameter cmd_i2 : cmd ops -> cmd ops.

Fixpoint prod_cmd' (c:cmd ops) : cmd ops :=
 match c with
 | Skip => @Skip _
 | Assume e => Seq (Assume (expr_i1 e)) (Assume (expr_i2 e))
 | Assert e => Seq (Assert (expr_i1 e)) (Assert (expr_i2 e))
 | Assign l e =>
    Seq (check (And (EqLeak (ValOf (lvalue_i1 l)) (ValOf (lvalue_i2 l)))
                    (EqLeak (expr_i1 e) (expr_i2 e))))
        (Seq (Assign (lvalue_i1 l) (expr_i1 e))
             (Assign (lvalue_i2 l) (expr_i2 e)))
 | Seq c1 c2 => Seq (prod_cmd' c1) (prod_cmd' c2)
 | If b c1 c2 => 
    Seq (checkTest (expr_i1 b) (expr_i2 b))
        (If (ValOf (Var _ xH))
            (If (expr_i1 b) (prod_cmd' c1) (prod_cmd' c2))
            (Seq (If (expr_i1 b) (cmd_i1 c1) (cmd_i1 c2))
                 (If (expr_i2 b) (cmd_i2 c1) (cmd_i2 c2))))
 | While b c =>
    Seq (checkTest (expr_i1 b) (expr_i2 b))
        (Seq (While (And (ValOf (Var _ xH)) (expr_i1 b))
                    (Seq (prod_cmd' c)
                         (checkTest (expr_i1 b) (expr_i2 b))))
             (Seq (While (expr_i1 b) (cmd_i1 c))
                  (While (expr_i2 b) (cmd_i2 c))))
 end.

Fixpoint prod_cmd2 (c:cmd ops) : cmd ops :=
 match c with
 | Skip => @Skip _
 | Assume e => Seq (Assume (expr_i1 e)) (Assume (expr_i2 e))
 | Assert e => Seq (Assert (expr_i1 e)) (Assert (expr_i2 e))
 | Assign l e =>
    Seq (check (And (EqLeak (ValOf (lvalue_i1 l)) (ValOf (lvalue_i2 l)))
                    (EqLeak (expr_i1 e) (expr_i2 e))))
        (Seq (Assign (lvalue_i1 l) (expr_i1 e))
             (Assign (lvalue_i2 l) (expr_i2 e)))
 | Seq c1 c2 => Seq (prod_cmd2 c1) (prod_cmd2 c2)
 | If b c1 c2 =>
    If (expr_i1 b)
       (Seq (checkTest (expr_i1 b) (expr_i2 b))
            (If (ValOf (Var _ xH))
                (prod_cmd2 c1)
                (Seq (cmd_i1 c1)
                     (If (expr_i2 b)
                         (cmd_i2 c1)
                         (cmd_i2 c2)))))
       (Seq (checkTest (expr_i1 b) (expr_i2 b))
            (If (ValOf (Var _ xH))
                (prod_cmd2 c2)
                (Seq (cmd_i1 c2)
                     (If (expr_i2 b)
                         (cmd_i2 c1)
                         (cmd_i2 c2)))))
 | While b c =>
    While (Or (expr_i1 b) (expr_i2 b))
          (Seq (checkTest (expr_i1 b) (expr_i2 b))
               (If (ValOf (Var _ xH))
                   (Seq (prod_cmd2 c)
                        (checkTest (expr_i1 b) (expr_i2 b)))
                   (Seq (While (expr_i1 b) (cmd_i1 c))
                        (While (expr_i2 b) (cmd_i2 c)))))
 end.



Lemma prod_cmd_complete2: forall c st1 st2 b l st',
 eval_cmd lspec (joinState st1 st2 b) (prod_cmd2 c) l (Some st') ->
 exists (l1 l2: Leakage),
  eval_cmd lspec st1 c l1 (Some (splitState st').1.1) /\
  eval_cmd lspec st2 c l2 (Some (splitState st').1.2) /\
  ((splitState st').2!=0 -> l1=l2).
Proof.
move => c st1 st2 b l st'.
move: {1 3}(Some st') (eqstateOpt_refl (Some st')) => os Es.
move: {1 3}(prod_cmd2 c) (Logic.eq_refl (prod_cmd2 c))
=> c' E H.
elim: H st' Es c E => {os l c'}.
admit.
admit.
admit.
admit.
admit.
(* Seq *)
move=> sta stb ss c1 c2 l1 l2 H1 IH1 H2 IH2.
 admit.
(* Seq Fail *)
move=> sta c1 c2 l1 H1 IH1 //=.
(* If True *)
move=> sa ssa ba c1 c2 l1 Hba H1 IH1.
(*
 Hba : isTrue_expr sa ba
  H1 : eval_cmd lspec sa c1 l1 ssa
  IH1 : forall st' : State,
        eqstateOpt ssa (Some st') ->
        forall c : cmd ops,
        c1 = prod_cmd2 c ->
        exists l0 l2 : Leakage,
          eval_cmd lspec st1 c l0 (Some (splitState st').1.1) /\
          eval_cmd lspec st2 c l2 (Some (splitState st').1.2) /\
          ((splitState st').2 != 0 -> l0 = l2)
  ============================
   forall st' : State,
   eqstateOpt ssa (Some st') ->
   forall c : cmd ops,
   If ba c1 c2 = prod_cmd2 c ->
   exists l0 l2 : Leakage,
     eval_cmd lspec st1 c l0 (Some (splitState st').1.1) /\
     eval_cmd lspec st2 c l2 (Some (splitState st').1.2) /\
     ((splitState st').2 != 0 -> l0 = l2)
*)
admit.
(* If False *)
admit.
(* While True *)
move => sa sb ss cond c l1 l2 Hba H1 IH1
H2 IH2.
(*
 Hba : isTrue_expr sa cond
  H1 : eval_cmd lspec sa c l1 (Some sb)
  IH1 : forall st' : State,
        eqstateOpt (Some sb) (Some st') ->
        forall c0 : cmd ops,
        c = prod_cmd2 c0 ->
        exists l0 l3 : Leakage,
          eval_cmd lspec st1 c0 l0 (Some (splitState st').1.1) /\
          eval_cmd lspec st2 c0 l3 (Some (splitState st').1.2) /\
          ((splitState st').2 != 0 -> l0 = l3)
  H2 : eval_cmd lspec sb (While cond c) l2 ss
  IH2 : forall st' : State,
        eqstateOpt ss (Some st') ->
        forall c0 : cmd ops,
        While cond c = prod_cmd2 c0 ->
        exists l0 l3 : Leakage,
          eval_cmd lspec st1 c0 l0 (Some (splitState st').1.1) /\
          eval_cmd lspec st2 c0 l3 (Some (splitState st').1.2) /\
          ((splitState st').2 != 0 -> l0 = l3)
  ============================
   forall st' : State,
   eqstateOpt ss (Some st') ->
   forall c0 : cmd ops,
   While cond c = prod_cmd2 c0 ->
   exists l0 l3 : Leakage,
     eval_cmd lspec st1 c0 l0 (Some (splitState st').1.1) /\
     eval_cmd lspec st2 c0 l3 (Some (splitState st').1.2) /\
     ((splitState st').2 != 0 -> l0 = l3)
*)
admit.
(* While Fail *)
by [].
(* While False *)
admit.
Qed.









Lemma prod_cmdA: forall c,
 assertionCmd (prod_cmd c) = false.
Proof. by move => [||||||]. Qed.

(** A specialised induction principle for handling evaluation of the
   transformed program...                                                 *)
Lemma eval_prod_ind
  (P : State -> cmd ops -> Leakage -> State -> Prop)
  (Hskip: forall st st' : State, eqstate st st' -> P st (Skip ops) [::] st')
  (Hassume: forall (st st' : State) (e : expr ops),
             eqstate st st' ->
             isTrue_expr st (expr_i1 e) ->
             isTrue_expr st (expr_i2 e) -> P st (Assume e) [::] st')
  (Hassert: forall (st st' : State) (e : expr ops),
             eqstate st st' ->
             isTrue_expr st (expr_i1 e) ->
             isTrue_expr st (expr_i2 e) -> P st (Assert e) [::] st')
  (Hassign: forall (st st' : State) (x : lvalue ops) (e : expr ops),
             eqstate
              (updLValue
               (updLValue st (lvalue_i1 x) (eval_expr st (expr_i1 e)))
               (lvalue_i2 x) (eval_expr (updLValue st (lvalue_i1 x) (eval_expr st (expr_i1 e))) (expr_i2 e))) st' ->
             isTrue_expr st (EqLeak (expr_i1 (ValOf x)) (expr_i2 (ValOf x))) ->
             isTrue_expr st (EqLeak (expr_i1 e) (expr_i2 e)) ->
             P st (Assign x e)
               (leak_expr lspec st (expr_i1 (ValOf x)) ++
                leak_expr lspec st (expr_i1 e) ++
                leak_expr lspec
                    (updLValue st (lvalue_i1 x) (eval_expr st (expr_i1 e)))
                    (expr_i2 (ValOf x)) ++
                leak_expr lspec
                    (updLValue st (lvalue_i1 x) (eval_expr st (expr_i1 e)))
                    (expr_i2 e)) st')
  (Hseq: forall (st1 st2 st3 : State) (c1 c2 : cmd ops) (l1 l2 : Leakage),
          eval_cmd lspec st1 (prod_cmd c1) l1 (Some st2) ->
          P st1 c1 l1 st2 ->
          eval_cmd lspec st2 (prod_cmd c2) l2 (Some st3) ->
          P st2 c2 l2 st3 -> P st1 (Seq c1 c2) (l1 ++ l2) st3)
  (HifT: forall (st1 st2 : State) (b : expr ops) (c1 c2 : cmd ops) l1,
          isTrue_expr st1 (expr_i1 b) ->
          isTrue_expr st1 (EqLeak (expr_i1 b) (expr_i2 b)) ->
          isTrue_expr st1 (Equal (IsTrue (expr_i1 b)) (IsTrue (expr_i2 b))) ->
          eval_cmd lspec st1 (prod_cmd c1) l1 (Some st2) ->
          P st1 c1 l1 st2 ->
          P st1 (If b c1 c2)
            (leak_expr lspec st1 (expr_i1 b) ++ inl true :: l1) st2)
  (HifF: forall (st1 st2 : State) (b : expr ops) (c1 c2 : cmd ops) l1,
          ~~ isTrue_expr st1 (expr_i1 b) ->
          isTrue_expr st1 (EqLeak (expr_i1 b) (expr_i2 b)) ->
          isTrue_expr st1 (Equal (IsTrue (expr_i1 b)) (IsTrue (expr_i2 b))) ->
          eval_cmd lspec st1 (prod_cmd c2) l1 (Some st2) ->
          P st1 c2 l1 st2 ->
          P st1 (If b c1 c2)
            (leak_expr lspec st1 (expr_i1 b) ++ inl false :: l1) st2)
  (HwhileT: forall (st1 st2 st3 : State) (b : expr ops) (c : cmd ops) l1 l2,
          isTrue_expr st1 (expr_i1 b) ->
          isTrue_expr st1 (EqLeak (expr_i1 b) (expr_i2 b)) ->
          isTrue_expr st1 (Equal (IsTrue (expr_i1 b)) (IsTrue (expr_i2 b))) ->
          eval_cmd lspec st1 (prod_cmd c) l1 (Some st2) ->
          P st1 c l1 st2 ->
          isTrue_expr st2 (EqLeak (expr_i1 b) (expr_i2 b)) ->
          isTrue_expr st2 (Equal (IsTrue (expr_i1 b)) (IsTrue (expr_i2 b))) ->
          eval_cmd lspec st2 
               (While (expr_i1 b)
                 (Seq (prod_cmd c) (assertEqLeakTest (expr_i1 b) (expr_i2 b))))
               l2 (Some st3) ->
          P st2 (While b c) l2 st3 ->
          P st1 (While b c)
               (leak_expr lspec st1 (expr_i1 b) ++ inl true :: l1 ++ l2) st3)
  (HwhileF: forall (st st' : State) (b : expr ops) (c : cmd ops),
          eqstate st st' ->
          ~~ isTrue_expr st (expr_i1 b) ->
          isTrue_expr st (EqLeak (expr_i1 b) (expr_i2 b)) ->
          isTrue_expr st (Equal (IsTrue (expr_i1 b)) (IsTrue (expr_i2 b))) ->
          P st (While b c)
               (leak_expr lspec st (expr_i1 b) ++ [:: inl false]) st')
  : forall (s : State) (c : cmd ops) (l : Leakage) (s' : State),
   eval_cmd lspec s (prod_cmd c) l (Some s') -> P s c l s'.
Proof.
move => s c l s' H; move: (H).
move/eval_cmd_unsafe: H.
move: {1 3}(Some s') (eqstateOpt_refl (Some s')) => os Es.
move: {1 3}(unsafe (prod_cmd c)) (Logic.eq_refl (unsafe (prod_cmd c)))
=> c' E H.
elim: H s' Es c E => {os s l c'}
 [ st st' EqS1
 | st st' e EqS1 Ee
 | st st' e EqS1 Ee | st e Ee
 | st st' x e EqS1
 | sta1 sta2 [sta3|] c1 c2 l1 l2 H1 IH1 H2 IH2
 | sta1 c1 c2 l1 l2 IH
 | st st' b c1 c2 l1 Eb H1 IH1
 | st st' b c1 c2 l1 Eb H IH
 | st st' st'' b c' l1' l2' Eb H1 IH1 H2 IH2
 | st b c' l' Eb H1 IH 
 | st st' b c' Eb EqS1] s //= Es c Ec Heval. 
- (* skip *)
move: c Ec Heval => [|e|e|? ?|? ?|? ? ?|? ?] /= Ec;
(discriminate Ec || subst).
   (* skip *)
   by move=> _; apply Hskip; rewrite EqS1.
  (* assume *)
  move=> /= /eval_cmd_SeqSI [s' [l1' [l2' [H1 H2 _]]]].
  move/eval_cmd_AssumeI: H1 => [Te1 /= Es1 _].
  move/eval_cmd_AssumeI: H2 => [Te2 /= Es2 _].
  by apply Hassume => //; rewrite Es1.
 (* assert *)
 move=> /= /eval_cmd_SeqSI [s' [l1' [l2' [H1 H2 _]]]].
 move/eval_cmd_AssertSI: H1 => [Te1 /= Es1 _].
 move/eval_cmd_AssertSI: H2 => [Te2 /= Es2 _].
 by apply Hassert => //; rewrite Es1.
(* seq *)
rewrite !prod_cmdA in Ec; discriminate Ec.
- (* assume *)
move: c Ec Heval => [|?|?|? ?|? ?|? ? ?|? ?] /= Ec; 
rewrite /= ?prod_cmdA in Ec; discriminate Ec.
- (* assertT *)
move: c Ec Heval => [|?|?|? ?|? ?|? ? ?|? ?] /= Ec; 
rewrite /= ?prod_cmdA in Ec; discriminate Ec.
- (* assign *)
move: c Ec Heval => [|?|?|? ?|? ?|? ? ?|? ?] /= Ec; 
rewrite /= ?prod_cmdA in Ec; discriminate Ec.
- (* seqS *)
move: c Ec Heval => [|?|?|xa ea|ca cb|? ? ?|? ?] /= Ec;
(discriminate Ec || move: Ec).
 (* assign *)
 move=> [Ec1 Ec2]; subst.
 move=> /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb El1]]]].
 move: Ha => /eval_cmd_AssertSI.
 rewrite isTrue_And => [[/andP[Ha1 Ha2] Ha3 Ha4]].
 move: Hb => /eval_cmd_SeqSI [sb1 [lb1 [lb2 [Hb Hc El2]]]].
 move: Hb => /eval_cmd_AssignI [/= Hb1 Hb2].
 move: Hc => /eval_cmd_AssignI [/= Hc1 Hc2]; subst.
 rewrite El1 /= -!Ha3 -!catA.
 change (ValOf (lvalue_i1 xa)) with (expr_i1 (ValOf xa)).
 change (ValOf (lvalue_i2 xa)) with (expr_i2 (ValOf xa)).
 rewrite Hb1 -Ha3; apply Hassign => //.
 by rewrite Hc1 Hb1 Ha3.
(* seq *)
rewrite /= ?prod_cmdA => /= [[Ec1 Ec2] Heval]; subst.
move: Heval => /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb _]]]].
move: {H1} (eval_cmd_determ H1 (eval_cmd_unsafe Ha) (eqstate_refl sta1))
=> [El1 /= Es1].
move: {H2} (eval_cmd_determ H2 (eval_cmd_unsafe Hb) Es1) => [El2 /= H2]; subst.
apply Hseq with sta2 => //.
   by rewrite Es1.
  by apply IH1; rewrite // Es1.
 by rewrite Es1.
by apply IH2; rewrite // Es1.
- (* ifT *)
move: c Ec Heval => [|?|?|? ?|? ?|b' ca cb|? ?] /= Ec;
(discriminate Ec || move: Ec).
 (* seq *)
 rewrite !prod_cmdA => Ec; discriminate Ec.
(* if *)
move=> /= [Ec1 [Ec2 Ec3]]; subst.
move=> /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb _]]]].
move: Ha => /eval_cmd_AssertSI.
rewrite isTrue_And => [[/andP[Ha1 Ha2] Ha3 Ha4]].
move: Hb => /eval_cmd_IfI [l'].
rewrite -> Ha3 in Eb; rewrite Eb.
move => [Hb1 Hb2].
move: {H1} (eval_cmd_determ H1 (eval_cmd_unsafe Hb1) Ha3) => [El2 H1]; subst.
apply HifT => //.
  by rewrite Ha3.
 by rewrite Ha3.
apply IH1 => //.
by rewrite Ha3.
- (* ifF *)
move: c Ec Heval => [|?|?|? ?|? ?|b' ca cb|? ?] /= Ec;
(discriminate Ec || move: Ec).
 (* seq *)
 rewrite !prod_cmdA => Ec; discriminate Ec.
(* if *)
move=> /= [Ec1 [Ec2 Ec3]]; subst.
move=> /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb _]]]].
move: Ha => /eval_cmd_AssertSI.
rewrite isTrue_And => [[/andP[Ha1 Ha2] Ha3 Ha4]].
move: Hb => /eval_cmd_IfI [l'].
rewrite -> Ha3 in Eb; rewrite (negPf Eb).
move => [Hb1 Hb2].
move: {H} (eval_cmd_determ H (eval_cmd_unsafe Hb1) Ha3) => [El2 H]; subst.
apply HifF => //.
  by rewrite Ha3.
 by rewrite Ha3.
apply IH => //.
by rewrite Ha3.
- (* whileT *) 
move: c Ec Heval => [|?|?|? ?|? ?|? ? ?|ba ca] /= Ec;
(discriminate Ec || move: Ec).
 (* seq *)
 rewrite !prod_cmdA => Ec; discriminate Ec.
(* whileT *)
move=> [Ec1 Ec2]; rewrite prod_cmdA in Ec2 ; subst.
move=> /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb _]]]].
move: Ha => /eval_cmd_AssertSI. 
rewrite isTrue_And => [[/andP[Ha1 Ha2] Ha3 Ha4]].
move: Hb => /eval_cmd_WhileSI.
rewrite -> Ha3 in Eb; rewrite Eb.
move=> [sb [lb1 [lb2 [Hb1 Hb2 Hb3]]]].
move: Hb1 => /eval_cmd_SeqSI [sc [lc1 [lc2 [Hc1]]]].
move=> /eval_cmd_AssertSI.
rewrite isTrue_And; move=> [/andP [Hc2 Hc3] Hc4] Hc5 Hc6; subst.
move: {H1} (eval_cmd_determ H1 (eval_cmd_unsafe Hc1) Ha3) => [El2 /=H1].
move: (eval_cmd_unsafe Hb2); rewrite /= !prod_cmdA => H2'.
rewrite -> Hc4 in H1; move: {H2} (eval_cmd_determ H2 H2' H1).
rewrite Es /=; move=> [El3 /= H2]; subst.
apply HwhileT with st' => //.
      by rewrite Ha3.
     by rewrite Ha3 H1 -Hc4.
    apply IH1 => //=.
    by rewrite Ha3 H1 -Hc4.
   by rewrite H1 -Hc4.
  by rewrite H1 -Hc4.
 by rewrite H1.
apply IH2 => //=; first by rewrite !prod_cmdA.
change lb2 with ([::]++lb2).
apply eval_SeqS with st'.
 constructor => //.
 by rewrite H1 -Hc4 isTrue_And; apply/andP; split.
by rewrite H1.
- (* whileF *)
move: c Ec Heval => [|?|?|? ?|? ?|? ? ?|ba ca] /= Ec;
(discriminate Ec || move: Ec).
 (* seq *)
 rewrite !prod_cmdA => Ec; discriminate Ec.
(* whileF *)
move=> [Ec1 Ec2]; rewrite prod_cmdA in Ec2 ; subst.
move=> /eval_cmd_SeqSI [sa1 [la1 [la2 [Ha Hb _]]]].
move: Ha => /eval_cmd_AssertSI.
rewrite isTrue_And => [[/andP[Ha1 Ha2] Ha3] Ha4].
move: Hb => /eval_cmd_WhileSI.
rewrite -> Ha3 in Eb; rewrite (negPf Eb); move => [Hb1 Hb2]; subst.
apply HwhileF => //=.
 by rewrite EqS1 Es.
by rewrite Ha3.
Qed.

Lemma prod_cmd_sound': forall st1 c l1 st1' st2 l2 st2',
 eval_cmd lspec st1 c l1 (Some st1') ->
 eval_cmd lspec st2 c l2 (Some st2') ->
 l1 == l2 ->
 exists l : Leakage,
  eval_cmd lspec (joinState st1 st2) 
           (prod_cmd c) l (Some (joinState st1' st2')).
Proof.
move => st1 c l1 st1' st2 l2 st2'.
move: {1 3}(Some st1') (eqstateOpt_refl (Some st1')) => os Eos H1.
elim: H1 st1' Eos st2 l2 st2'
=> [ sta stb EqSab
   | sta stb e EqSab Ee
   | sta stb e EqSab Ee | sta e Ee
   | sta stb x e EqSab
   | sta stb stc ca cb la lb Ha /= IHa Hb IHb
   | sta c1 c2 la lb /= IH
   | sta stb b ca cb la Eb Ha /= IHa
   | sta stb b ca cb lb Eb Hb /= IHb
   | sta stb stc b cb la lb Eb Ha /= IHa Hb IHb
   | sta b cb lb Eb Ha IHa 
   | sta stb b cb Eb EqSab] st1' //= Es1' st2 l2 st2'.
- (* Skip *)
move=> /eval_cmd_SkipI [/= EqS _] _.
exists [::]; constructor.
by rewrite EqSab Es1' EqS.
- (* Assume *)
move=> /eval_cmd_AssumeI [H /= EqS _] _.
exists ([::]++[::]); apply eval_SeqS with (joinState sta st2).
 constructor => //.
 by rewrite /isTrue_expr eval_expr_join_i1.
constructor => //.
 by rewrite EqSab Es1' EqS.
by rewrite /isTrue_expr eval_expr_join_i2.
- (* AssertS *)
move=> /eval_cmd_AssertSI [H /= EqS _] _.
exists ([::]++[::]); apply eval_SeqS with (joinState sta st2).
 constructor => //.
 by rewrite /isTrue_expr eval_expr_join_i1.
constructor => //.
 by rewrite EqSab Es1' EqS.
by rewrite /isTrue_expr eval_expr_join_i2.
- (* Assign *)
move=> /eval_cmd_AssignI [//= Es1 ->].
rewrite eqleak_split => /andP [El1 El2].
exists ([::]++
   (leak_expr lspec (joinState sta st2) (expr_i1 (ValOf x))
    ++leak_expr lspec (joinState sta st2) (expr_i1 e))
    ++(leak_expr lspec (joinState (updLValue sta x (eval_expr sta e)) st2) (expr_i2 (ValOf x))
    ++leak_expr lspec (joinState (updLValue sta x (eval_expr sta e)) st2) (expr_i2 e))).
apply eval_SeqS with (joinState sta st2).
 constructor => //.
 change (ValOf (lvalue_i1 x)) with (expr_i1 (ValOf x)).
 change (ValOf (lvalue_i2 x)) with (expr_i2 (ValOf x)).
 rewrite isTrue_And; apply/andP; split.
  by rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
 by rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
apply eval_SeqS with (joinState stb st2).
 constructor => //.
 by rewrite updLValue_join_i1 eval_expr_join_i1 EqSab.
rewrite !EqSab; constructor => //.
by  rewrite updLValue_join_i2 eval_expr_join_i2 -Es1 Es1'.
- (* seq *)
move=> /eval_cmd_SeqI [[//= H1 H2] H3|[s' [l1' [l2' [H1 H2 H3 H4]]]]]; subst.
move: {H4} (eval_cmd_leak_split Ha H1 H4) => /andP [/eqP El1 /eqP El2]; subst.
move: {IHa Ha H1} (IHa _ (eqstate_refl stb) _ _ _ H1 (eq_refl _)).
move=> [lta Hta].
rewrite -> Es1' in Hb.
move: {IHb Hb H2} (IHb _ Es1' _ _ _ H2 (eq_refl _)).
move=> [ltb Htb].
by exists (lta++ltb); apply eval_SeqS with (joinState stb s').
- (* ifT *)
move=> /eval_cmd_IfI [l'].
case/boolP: (isTrue_expr st2 b); last first.
 by move=> _ [_ ->]; rewrite eqleak_split !eqE /= andbF.
move=> Eb' [H1 El2]; rewrite El2 eqleak_split !eqE /= =>/andP[El El'].
move: {IHa Ha H1} (IHa _ Es1' _ _ _ H1 El') => [lta Hta].
exists ([::] ++ (leak_expr lspec (joinState sta st2) (expr_i1 b) ++ inl true :: lta)); apply eval_SeqS with (joinState sta st2).
 constructor => //.
 rewrite isTrue_And isTrue_Equal; apply/andP; split.
  rewrite !eval_IsTrue eval_expr_join_i1 eval_expr_join_i2. 
  by move: Eb Eb'; rewrite /isTrue_expr => /negPf -> /negPf ->.
 by rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
constructor => //.
by rewrite /isTrue_expr eval_expr_join_i1.
- (* ifF *)
move=> /eval_cmd_IfI [l'].
case/boolP: (isTrue_expr st2 b).
 by move=> _ [_ ->]; rewrite eqleak_split !eqE /= andbF.
move=> Eb' [H1 El2]; rewrite El2 eqleak_split !eqE /= =>/andP[El El'].
move: {IHb Hb H1} (IHb _ Es1' _ _ _ H1 El') => [ltb Htb].
exists ([::] ++ (leak_expr lspec (joinState sta st2) (expr_i1 b) ++ inl false :: ltb)); apply eval_SeqS with (joinState sta st2).
 constructor => //.
 rewrite isTrue_And isTrue_Equal; apply/andP; split.
  rewrite !eval_IsTrue eval_expr_join_i1 eval_expr_join_i2. 
  by move: Eb Eb'; rewrite /isTrue_expr => /negPn -> /negPn ->.
 by rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
constructor => //.
by rewrite /isTrue_expr eval_expr_join_i1.
- (* whileT *)
move=> /eval_cmd_WhileSI; case/boolP: (isTrue_expr st2 b); last first.
 by move=> _ [_ ->]; rewrite eqleak_split !eqE /= andbF.
move=> Eb' [s' [l1' [l2' [H1 H2 El2]]]].
rewrite El2 eqleak_split !eqE /= =>/andP [Eleak Ell].
move: {Ell} (eval_cmd_leak_split Ha H1 Ell) => /andP [Ela Elb].
move: {IHa Ha H1} (IHa _ (eqstate_refl stb) _ _ _ H1 Ela) => [lta Hta].
move: {IHb Hb H2} (IHb _ Es1' _ _ _ H2 Elb) => [ltb].
move=> /eval_cmd_SeqSI [sb [ltb1 [ltb2 []]]].
move=> /eval_cmd_AssertSI [Hleak2 <- -> Htb /= Eltb].
exists ([::] ++ (leak_expr lspec (joinState sta st2) (expr_i1 b) ++ inl true :: lta ++ ltb)).
apply eval_SeqS with (joinState sta st2).
 constructor => //.
 rewrite isTrue_And isTrue_Equal; apply/andP; split.
  rewrite !eval_IsTrue eval_expr_join_i1 eval_expr_join_i2. 
  by move: Eb Eb'; rewrite /isTrue_expr => /negPf -> /negPf ->.
 by rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
apply eval_WhileTS with (joinState stb s') => //.
  by rewrite /isTrue_expr eval_expr_join_i1.
 rewrite -[lta]cats0.
 apply eval_SeqS with (joinState stb s') => //.
 by constructor.
by rewrite Eltb.
- (* whileF *)
move=> /eval_cmd_WhileSI; case/boolP: (isTrue_expr st2 b).
 by move=> _ [? [? [? [_ _ ->]]]]; rewrite eqleak_split !eqE /= andbF.
move=> Eb' [Es2 ->] El.
exists ([::]++(leak_expr lspec (joinState sta st2) (expr_i1 b) ++ [:: inl false])).
apply eval_SeqS with (joinState sta st2); constructor => //.
  rewrite isTrue_And; apply/andP; split.
   rewrite /isTrue_expr eval_Equal !eval_IsTrue
           eval_expr_join_i1 eval_expr_join_i2. 
   by move: Eb Eb'; rewrite /isTrue_expr => /negPn -> /negPn ->.
  rewrite isTrue_EqLeak; apply/eqP; rewrite preleak_prod.
  by move: El; rewrite eqleak_split => /andP [? _].
 by rewrite /isTrue_expr eval_expr_join_i1.
by rewrite EqSab Es1' Es2.
Qed.

Lemma prod_cmd_complete': forall c st1 st2 l st',
 eval_cmd lspec (joinState st1 st2) (prod_cmd c) l (Some st') ->
 exists (l: Leakage),
  eval_cmd lspec st1 c l (Some (splitState st').1) /\
  eval_cmd lspec st2 c l (Some (splitState st').2).
Proof.
move => c st1 st2 l st'.
move: {1 3}(joinState st1 st2) (eqstate_refl (joinState st1 st2)).
move => s12 Es12 H.
move: H st1 st2 Es12.
pose P s12 c (l:Leakage) st' := forall st1 st2 : State,
   eqstate s12 (joinState st1 st2) ->
   exists l: Leakage,
     eval_cmd lspec st1 c l (Some (splitState st').1) /\
     eval_cmd lspec st2 c l (Some (splitState st').2).
apply (@eval_prod_ind P); rewrite /P {c l s12 st' P}.
(* skip *)
move=> sa sb Es s1 s2 Es'.
exists [::].
by rewrite -!Es !Es' split_joinState_1 split_joinState_2; split; constructor.
(* assume *)
move=> sa sb e Es Ee1 Ee2 s1 s2 Es'.
exists [::].
rewrite -!Es !Es' split_joinState_1 split_joinState_2; split; constructor=> //.
 by move: Ee1; rewrite Es' /isTrue_expr eval_expr_join_i1.
by move: Ee2; rewrite Es' /isTrue_expr eval_expr_join_i2.
(* assert *)
move=> sa sb e Es Ee1 Ee2 s1 s2 Es'.
exists [::].
rewrite -!Es !Es' split_joinState_1 split_joinState_2; split; constructor=> //.
 by move: Ee1; rewrite Es' /isTrue_expr eval_expr_join_i1.
by move: Ee2; rewrite Es' /isTrue_expr eval_expr_join_i2.
(* assign *)
move=> sa sb x e Es El1 El2 s1 s2 Es'.
exists (leak_expr lspec s1 (ValOf x)
        ++leak_expr lspec s1 e).
split.
 constructor.
 rewrite -Es Es' updLValue_join_i1 updLValue_join_i2 split_joinState_1.
 by rewrite eval_expr_join_i1.
move: El1 El2; rewrite !Es' !isTrue_EqLeak => /eqP El1 /eqP El2.
move: El1; rewrite preleak_prod => /eqP ->.
move: El2; rewrite preleak_prod => /eqP ->.
constructor.
rewrite -Es Es' updLValue_join_i1 updLValue_join_i2 split_joinState_2.
by rewrite eval_expr_join_i2.
(* seq *)
move=> sa sb sc c1 c2 l1 l2 H1 IH1 H2 IH2 s1 s2 Es.
move: {IH1} (IH1 _ _ Es) => [lta [Hta1 Hta2]].
move: {IH2} (IH2 (splitState sb).1 (splitState sb).2 (eqstate_sym (join_splitState sb))) => [ltb [Htb1 Htb2]].
exists (lta++ltb); split.
 by apply eval_SeqS with (splitState sb).1.
by apply eval_SeqS with (splitState sb).2.
(* ifT *)
move=> sa sb b c1 c2 l1 Eb El Eeqb H1 IH1 s1 s2 Es.
move: {IH1} (IH1 _ _ Es) => [lta [Hta1 Hta2]].
exists (leak_expr lspec s1 b ++ inl true :: lta); split.
 constructor => //.
 by move: Eb; rewrite Es /isTrue_expr eval_expr_join_i1.
move: El; rewrite !Es isTrue_EqLeak => /eqP El. 
move: El; rewrite preleak_prod => /eqP ->.
constructor => //.
move: Eb; rewrite /isTrue_expr -(@eval_expr_join_i2 _ b s1 s2) => Eb.
move: Eeqb; rewrite isTrue_Equal !eval_IsTrue (negPf Eb).
case: (ifP _) => // /negP H _. 
by move: H; rewrite Es => H; apply/negP.
(* ifF *)
move=> sa sb b c1 c2 l1 Eb El Eeqb H1 IH1 s1 s2 Es.
move: {IH1} (IH1 _ _ Es) => [lta [Hta1 Hta2]].
exists (leak_expr lspec s1 b ++ inl false :: lta); split.
 constructor => //.
 by move: Eb; rewrite Es /isTrue_expr eval_expr_join_i1.
move: El; rewrite !Es isTrue_EqLeak => /eqP El. 
move: El; rewrite preleak_prod => /eqP ->.
constructor => //.
move: Eb; rewrite /isTrue_expr -(@eval_expr_join_i2 _ b s1 s2) => /negPn Eb.
move: Eeqb; rewrite isTrue_Equal !eval_IsTrue /eqP Eb.
case: (ifP _) => // H _.
by move: H; rewrite Es => H; apply/negPn.
(* whileT *)
move=> sa sb sc b c l1 l2 Eb Ela Eea H1 IH1 Elb Eeb H2 IH2 s1 s2 Es.
move: {IH1} (IH1 _ _ Es) => [lta [Hta1 Hta2]].
move: {IH2} (IH2 (splitState sb).1 (splitState sb).2 (eqstate_sym (join_splitState sb))) => [ltb [Htb1 Htb2]].
exists (leak_expr lspec s1 b ++ inl true:: lta++ltb); split.
 apply eval_WhileTS with (splitState sb).1 => //.
 by move: Eb; rewrite Es /isTrue_expr eval_expr_join_i1.
move: Ela; rewrite !Es isTrue_EqLeak => /eqP Ela.
move: Ela; rewrite preleak_prod => /eqP ->.
apply eval_WhileTS with (splitState sb).2 => //.
move: Eb; rewrite /isTrue_expr -(@eval_expr_join_i2 _ b s1 s2).
move: Eea; rewrite isTrue_Equal !eval_IsTrue Es
                   eval_expr_join_i1 eval_expr_join_i2.
by case: (ifP _); case: (ifP _).
(* whileF *)
move=> sa sb b c Es Eb El Eeqb s1 s2 Es'.
exists (leak_expr lspec s1 b ++ [:: inl false]); split.
 constructor.
  by move: Eb; rewrite Es' /isTrue_expr eval_expr_join_i1.
 by rewrite -Es Es' split_joinState_1.
move: El; rewrite !Es' isTrue_EqLeak => /eqP El. 
move: El; rewrite preleak_prod => /eqP ->.
constructor => //.
 move: Eeqb Eb; rewrite Es' isTrue_Equal !eval_IsTrue /isTrue_expr 
                   eval_expr_join_i1 eval_expr_join_i2.
 by case: (ifP _); case: (ifP _).
by rewrite -Es Es' split_joinState_2.
Qed.

Theorem prod_cmd_sound_and_complete:
 forall c lowInputs,
  Safe lspec (joinStateEqLow lowInputs) (prod_cmd c)
  <-> strict_leakSecure lspec lowInputs c.
Proof.
move => c lowIn; split.
 rewrite /Safe /joinStateEqLow => H st1 st2 EsLow.
 have HH: eqstateR lowIn (splitState (joinState st1 st2)).1
                         (splitState (joinState st1 st2)).2.
  by rewrite split_joinState_1 split_joinState_2.
 move: {H} (H _ HH) => [ss [ll H]].
 move: (prod_cmd_complete' H) => [l [H1 H2]].
 exists (splitState ss).1, (splitState ss).2, l, l.
 split => //; split => //.
rewrite /strict_leakSecure /leakSecure /Safe => H st Hst.
have HH: eqstateR lowIn (splitState st).1 (splitState st).2.
 by move: Hst; rewrite /joinStateEqLow.
move: (H _ _ HH) => [s1 [s2 [l1 [l2 [H1 [H2 H3]]]]]].
have H3': eqstateR lowVars0 s1 s2.
 by rewrite /eqstateR /lowVars0 /= => x; split.
move: {H3 H3'} (H3 H3') H1 H2 => /eqP H3 H1 H2.
exists (joinState s1 s2).
move: (@prod_cmd_sound' _ _ _ _ _ _ _ H1 H2 H3) => [ll].
by rewrite join_splitState => Hll; exists ll.
Qed.

End ProdTrf.

