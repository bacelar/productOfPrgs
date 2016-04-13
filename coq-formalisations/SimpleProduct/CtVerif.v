Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang ProductTrf.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section CTLeak.

Variable ops: opSig.

(** * A leakage-specification for the constant-time policy 

    The evaluation of expressions leak:
     - the identifiers of the accessed variables;
     - the identifiers and indexes (offsets) of array accesses.
*)
Fixpoint ctleak_expr (e:expr ops) : seq (expr ops) :=
 match e with
 | ValOf l => ctleak_lvalue l
 | Const _ => [::]
 | Minus e1 e2 | Mult e1 e2 | Equal e1 e2 =>
    ctleak_expr e1 ++ ctleak_expr e2
 | Op o args => ctleak_texpr args
 end
with ctleak_texpr {n} (t:texpr ops n) : seq (expr ops) :=
 match t with
 | t_nil => [::]
 | t_cons _ x l => ctleak_expr x ++ ctleak_texpr l
 end
with ctleak_lvalue x : seq (expr ops) :=
 match x with
 | Var v => [:: Const _ (Zpos v)]
 | ArrCell a e => [:: Const _ (Zpos a) ; e] ++ ctleak_expr e
 end.

Lemma ctleak_Minus: forall (e1 e2:expr ops),
 ctleak_expr (Minus e1 e2) = ctleak_expr e1 ++ ctleak_expr e2.
Proof. by []. Qed.

Lemma ctleak_Mult: forall (e1 e2:expr ops),
 ctleak_expr (Mult e1 e2) = ctleak_expr e1 ++ ctleak_expr e2.
Proof. by []. Qed.

Lemma ctleak_Equal: forall (e1 e2:expr ops),
 ctleak_expr (Equal e1 e2) = ctleak_expr e1 ++ ctleak_expr e2.
Proof. by []. Qed.

Lemma ctleak_tcons: forall (e:expr ops) n (l:texpr ops n),
 ctleak_texpr (t_cons e l) = ctleak_expr e ++ ctleak_texpr l.
Proof. by []. Qed.

Lemma ctleak_ArrCell: forall a (e:expr ops),
 ctleak_lvalue (ArrCell a e) = [:: Const _ (Zpos a), e & ctleak_expr e].
Proof. by []. Qed.

(** * PreLeakage

    For verification purposes, a downgraded version of leakage specification
   is used (what we call "PreLeakage"). Preleakage is used in the verification
   assertions introduced by the product transformation.

   [ctpreleak_expr] differs from [ctleak_expr] because it does not
   leaks variables and array identifiers (only indexes of accessed arrays).
   Two properties are demanded on preleakage specification:
      1) be invariant under variable renaming;
      2) equality on the evaluation of preleakage for an expression
         in two different states implies equality of leakage.
*)
Fixpoint ctpreleak_expr (e:expr ops) : seq (expr ops) :=
 match e with
 | ValOf l => ctpreleak_lvalue l
 | Const _ => [::]
 | Minus e1 e2 | Mult e1 e2 | Equal e1 e2 =>
    ctpreleak_expr e1 ++ ctpreleak_expr e2
 | Op o args => ctpreleak_texpr args
 end
with ctpreleak_texpr {n} (t:texpr ops n) : seq (expr ops) :=
 match t with
 | t_nil => [::]
 | t_cons _ x l => ctpreleak_expr x ++ ctpreleak_texpr l
 end
with ctpreleak_lvalue l :=
 match l with
 | Var v => [::]
 | ArrCell a e => [:: e & ctpreleak_expr e]
 end.

Lemma ctpreleak_Minus: forall (e1 e2:expr ops),
 ctpreleak_expr (Minus e1 e2) = ctpreleak_expr e1 ++ ctpreleak_expr e2.
Proof. by []. Qed.

Lemma ctpreleak_Mult: forall (e1 e2:expr ops),
 ctpreleak_expr (Mult e1 e2) = ctpreleak_expr e1 ++ ctpreleak_expr e2.
Proof. by []. Qed.

Lemma ctpreleak_Equal: forall (e1 e2:expr ops),
 ctpreleak_expr (Equal e1 e2) = ctpreleak_expr e1 ++ ctpreleak_expr e2.
Proof. by []. Qed.

Lemma ctpreleak_tcons: forall (e:expr ops) n (l:texpr ops n),
 ctpreleak_texpr (t_cons e l) = ctpreleak_expr e ++ ctpreleak_texpr l.
Proof. by []. Qed.

Lemma ctpreleak_ArrCell: forall a (e:expr ops),
 ctpreleak_lvalue (ArrCell a e) = [:: e & ctpreleak_expr e].
Proof. by []. Qed.

(** Preleakage should commute with variable renaming... *)
Lemma ctpreleak_ren_expr: forall f (e:expr ops),
 ctpreleak_expr (ren_expr f e) = map (ren_expr f) (ctpreleak_expr e).
Proof.
move => f.
pose P1 e :=
 ctpreleak_expr (ren_expr f e) = map (ren_expr f) (ctpreleak_expr e).
pose P2 (n:nat) (e: texpr ops n) :=
 ctpreleak_texpr (ren_texpr f e) = map (ren_expr f) (ctpreleak_texpr e).
pose P3 x :=
 ctpreleak_lvalue (ren_lvalue f x) = map (ren_expr f) (ctpreleak_lvalue x).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3 => //.
(* Minus *)
move => e1 IH1 e2 IH2.
by rewrite ren_Minus !ctpreleak_Minus map_cat IH1 // IH2 //.
(* Minus *)
move => e1 IH1 e2 IH2.
by rewrite ren_Mult !ctpreleak_Mult map_cat IH1 // IH2 //.
(* Equal *)
move => e1 IH1 e2 IH2.
by rewrite ren_Equal !ctpreleak_Equal map_cat IH1 // IH2 //.
(* t_cons *)
move => n e IHe l IHl.
by rewrite ren_tcons !ctpreleak_tcons map_cat IHe // IHl //.
(* ArrCell *)
move => x e IHe.
by rewrite ren_ArrCell !ctpreleak_ArrCell IHe //.
Qed.

(** Preleakage main property  *)
Lemma ctpreleak_product: forall st1 st2 (e: expr ops),
 (leak_expr ctpreleak_expr st1 e == leak_expr ctpreleak_expr st2 e)
 =  (leak_expr ctleak_expr st1 e == leak_expr ctleak_expr st2 e).
Proof.
move => st1 st2.
pose P1 e :=
 (leak_expr ctpreleak_expr st1 e == leak_expr ctpreleak_expr st2 e)
 =  (leak_expr ctleak_expr st1 e == leak_expr ctleak_expr st2 e).
pose P2 (n:nat) (e: texpr ops n) :=
 (map (fun e => @inr bool _ (eval_expr st1 e)) (ctpreleak_texpr e) 
  == map (fun e => inr (eval_expr st2 e)) (ctpreleak_texpr e))
 =  (map (fun e => @inr bool _ (eval_expr st1 e)) (ctleak_texpr e)
     == map (fun e => inr (eval_expr st2 e)) (ctleak_texpr e)).
pose P3 x :=
 (map (fun e => @inr bool _ (eval_expr st1 e)) (ctpreleak_lvalue x) 
  == map (fun e => inr (eval_expr st2 e)) (ctpreleak_lvalue x))
 =  (map (fun e => @inr bool _ (eval_expr st1 e)) (ctleak_lvalue x)
     == map (fun e => inr (eval_expr st2 e)) (ctleak_lvalue x)).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3 => //.
(* Minus *)
rewrite /leak_expr => e1 IH1 e2 IH2.
by rewrite !ctpreleak_Minus !ctleak_Minus !map_cat !cat_map_eq; f_equal.
(* Mult *)
rewrite /leak_expr => e1 IH1 e2 IH2.
by rewrite !ctpreleak_Mult !ctleak_Mult !map_cat !cat_map_eq; f_equal.
(* Equal *)
rewrite /leak_expr => e1 IH1 e2 IH2.
by rewrite !ctpreleak_Equal !ctleak_Equal !map_cat !cat_map_eq; f_equal.
(* t_cons *)
rewrite /leak_expr => n e1 IH1 e2 IH2.
by rewrite !ctpreleak_tcons !ctleak_tcons !map_cat !cat_map_eq; f_equal.
(* Var *)
move => x.
by rewrite /leak_expr /eval_expr !eq_refl.
(* ArrCell *)
rewrite /leak_expr => x e IHe.
rewrite !ctpreleak_ArrCell !ctleak_ArrCell /=.
apply eq_boolP.
 move/eqP => [-> /eqP HH]; rewrite IHe in HH.
 by rewrite (eqP HH).
move/eqP => [-> /eqP HH]; rewrite -IHe in HH.
by rewrite (eqP HH).
Qed.

Definition ct_lspec : LeakSpec ops :=
 Build_LeakSpec ctpreleak_ren_expr ctpreleak_product.

End CTLeak.


Theorem ctVerif_sound_and_complete:
 forall ops c lowInputs,
  Safe (ct_lspec ops) (joinStateEqLow lowInputs) (prod_cmd (ct_lspec ops) c)
  <-> strict_leakSecure (ct_lspec ops) lowInputs c.
Proof. by move=> ops; apply prod_cmd_sound_and_complete. Qed.