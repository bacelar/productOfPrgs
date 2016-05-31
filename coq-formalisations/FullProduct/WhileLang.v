Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.

Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope Z_scope.

(* a useful lemma about lists *)
Lemma cat_map_eq: forall {A} {B:eqType} (f1 f2:A->B) (l1:seq A) (l2 l3:seq B),
 map f1 l1 ++ l2 == map f2 l1 ++ l3 = (map f1 l1 == map f2 l1) && (l2==l3).
Proof.
move=> A B f1 f2 l1 l2 l3; apply/eq_boolP.
 elim: l1 => //=.
 move => x xs IH /eqP [E1 /eqP E2].
 move: {IH E2} (IH E2) => /andP [/eqP E2 E3].
 by apply/andP; split => //; rewrite E1 E2.
by move => /andP [/eqP -> /eqP ->].
Qed.

(** Operations signature:

    For the sake of simplificy, we consider only operations over integers
  (boolean values are captured by testing equality with [0]). The semantics
  of each operation is specified by a function with type [seq Z -> Z] 
  (obs: it receives the arguments in reversed order, e.g. "e1 + e2" could
  be specified by the function
     [fun l => match l with [:: z2;z1] => z1+z2 | _ => 0]).
*)
Structure opSig := { ops:> finType
                   ; op_arity: ops -> nat
                   ; op_sem: ops -> seq Z -> Z
                   }.


(** Indentifiers (variable identifiers and array identifiers): *)
Definition ident := positive.


Section Syntax.

Variable op_sig : opSig.

Unset Elimination Schemes.

(** remark: a couple of operations are predefined in order to express
 the intended assertions in the transformation. All other ops are left
 abstract... *)
Inductive expr : Type :=
 | ValOf : lvalue -> expr	(* injection of lvalues *)
 | Const : Z -> expr		(* constant integer *)
 | Minus : expr -> expr -> expr	(* e1 - e2 *)
 | Mult : expr -> expr -> expr	(* e1 * e2 *)
 | Equal : expr -> expr -> expr (* e1 == e2 ? 1 : 0 *)
 | Op : forall (o:ops op_sig), texpr (op_arity o) -> expr
with texpr : nat -> Type :=
 | t_nil : texpr 0
 | t_cons : forall n (x:expr) (l:texpr n), texpr (S n)
with lvalue : Type :=
 | Var : ident -> lvalue
 | ArrCell : ident -> expr -> lvalue.

Scheme expr_mixed_ind := Induction for expr Sort Prop
 with texpr_mixed_ind := Induction for texpr Sort Prop
 with lvalue_mixed_ind := Induction for lvalue Sort Prop.

Combined Scheme expr_mutind 
 from expr_mixed_ind, texpr_mixed_ind, lvalue_mixed_ind.

Set Elimination Schemes.

(* Inversion principles for dependent arg-lists *)
Definition texpr0E (P:texpr 0 -> Type) (H:P t_nil) v:P v :=
match v with
  |t_nil => H
  |_ => fun devil => False_ind (forall A:Prop, A -> A) devil 
end.

Lemma texpr0I: forall (t:texpr 0), t=t_nil.
Proof. by apply texpr0E. Qed.

Definition texprSE (P:forall {n}, texpr n.+1 -> Type)
 (H:forall e {n} t, @P n (t_cons e t)) {n} (v:texpr n.+1) :P v :=
match v with
  | t_cons _ e t => H e t
  | _ => fun devil => False_ind (forall A:Prop, A -> A) devil 
end.

Lemma texprSI: forall n (t:texpr n.+1), exists e' t', t=t_cons e' t'.
Proof. by apply texprSE => e n t; exists e, t. Qed.

Definition texpr_cast o1 o2 (p:o1=o2)
 : texpr (@op_arity op_sig o1) -> texpr (op_arity o2) :=
 (fun f => eq_rect o1 (fun o => texpr (op_arity o1) -> texpr (op_arity o))
                   f o2 p) id.

Lemma texpr_cast_eq: forall o (E:o=o), texpr_cast E = id.
Proof.
rewrite /texpr_cast => o E.
rewrite -Eqdep_dec.eq_rect_eq_dec //.
move => {o E}o1 o2; case E: (o1==o2).
 by left; apply/eqP.
move/negP: E => E.
by right => H; apply E; apply/eqP.
Qed.

Fixpoint eq_expr e1 e2 :=
 match e1, e2 with
 | ValOf x1, ValOf x2 => eq_lvalue x1 x2
 | Const z1, Const z2 => z1==z2
 | Minus e11 e12, Minus e21 e22 => (eq_expr e11 e21) && (eq_expr e12 e22)
 | Mult e11 e12, Mult e21 e22 => (eq_expr e11 e21) && (eq_expr e12 e22)
 | Equal e11 e12, Equal e21 e22 => (eq_expr e11 e21) && (eq_expr e12 e22)
 | Op o1 te1, Op o2 te2 => if o2 =P o1 is ReflectT eq_oo
                           then eq_texpr te1 (texpr_cast eq_oo te2)
                           else false
 | _, _ => false
 end
with eq_texpr n (te1: texpr n) : texpr n -> bool :=
 match te1 in texpr nn return texpr nn -> bool with
 | t_nil => fun _ => true
 | t_cons _ e1 te1' =>
    fun te2 => (
     match te2 in texpr nn return (texpr nn.-1) -> bool with
     | t_cons _ e2 te2' => fun te1' => (eq_expr e1 e2) && (eq_texpr te1' te2')
     | _ => fun _ => false
     end te1')
 end
with eq_lvalue x1 x2 :=
 match x1, x2 with
 | Var v1, Var v2 => v1==v2
 | ArrCell a1 e1, ArrCell a2 e2 => (a1==a2) && (eq_expr e1 e2)
 | _, _ => false
 end.


Lemma eq_expr_refl: forall e, eq_expr e e.
Proof.
pose P1 e := eq_expr e e.
pose P2 n (t:texpr n) := eq_texpr t t.
pose P3 x := eq_lvalue x x.
apply (@expr_mixed_ind P1 P2 P3); rewrite /P1 /P2 /P3 //= {P1 P2 P3}. 
- by move => e1 -> e2 ->.
- by move => e1 -> e2 ->.
- by move => e1 -> e2 ->.
- move => o t H; elim eqP.
   by move => E; rewrite texpr_cast_eq.
  by [].
- by move => n e1 -> t1 ->.
- by move => a1 e1 ->; rewrite eq_refl.
Qed.

Lemma expr_eqP : Equality.axiom eq_expr.
Proof.
move=> e1 e2; apply/(iffP idP); last first.
 move => ->; apply eq_expr_refl.
pose P1 e1 := (forall e2, eq_expr e1 e2 -> e1=e2).
pose P2 n (t1:texpr n) :=
 (forall t2, eq_texpr t1 t2 -> t1=t2).
pose P3 x1 := (forall x2, eq_lvalue x1 x2 -> x1=x2).
move: e1 e2; apply (@expr_mixed_ind P1 P2 P3); unfold P1, P2, P3.
- move => x1 IH [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //= H.
  by f_equal; apply IH.
- by move => c1 [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //= /eqP ->.
- move => e11 IH1 e12 IH2 [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //=.
  by move => /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
- move => e11 IH1 e12 IH2 [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //=.
  by move => /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
- move => e11 IH1 e12 IH2 [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //=.
  by move => /andP [H1 H2]; rewrite (IH1 _ H1) (IH2 _ H2).
- move => o1 te1 IH [x2|c2|e21 e22|e21 e22|e21 e22|o2 te2] //=.
  case: (@eqP (Finite.eqType (ops op_sig)) o2 o1) => //.
  move => E H; apply IH in H; clear IH.
  move: te1 (E) H; rewrite -E {E o1} => te1 E ->.
  by rewrite texpr_cast_eq.
- move => t2 H.
  by symmetry; apply texpr0I.
- move => n e1 IHe t1 IHt tt2. 
  move: (texprSI tt2) => [e2 [t2 ->]] {tt2} /= /andP [/IHe H1 /IHt H2].
  by rewrite H1 H2.
- by move => v1 [v2|a2 e2] //= /eqP ->.
- move => a1 e1 IH [v2|a2 e2] //= /andP [/eqP -> /IH H2].
  by rewrite H2.
Qed.

Definition expr_eqMixin := EqMixin expr_eqP.
Canonical expr_eqType := Eval hnf in EqType expr expr_eqMixin.

Lemma lvalue_eqP: Equality.axiom eq_lvalue.
Proof.
move=> x1 x2; apply/(iffP idP).
 move: x1 x2 => [x1|a1 e1] [x2|a2 e2] => //=. 
  by move/eqP => [->].
 move => /andP [/eqP -> H].
 have: (e1==e2).
  by rewrite eqE.
 by move => /eqP ->. 
move: x1 x2 => [x1|a1 e1] [x2|a2 e2]; rewrite //=.
 by move => [->].
by move => [-> ->]; rewrite eq_refl /= eq_expr_refl.
Qed.

Definition lvalue_eqMixin := EqMixin lvalue_eqP.
Canonical lvalue_eqType := Eval hnf in EqType lvalue lvalue_eqMixin.

(** Useful derived operations *)
Definition Zero : expr := Const 0%Z.
Definition One : expr := Const 1%Z.
Definition Not (e: expr) : expr := Equal e Zero.
Definition IsTrue (e: expr) : expr := Minus One (Not e).
Definition And (e1 e2: expr) : expr := Mult (IsTrue e1) (IsTrue e2).
(** [EqSeqExpr] generates an assertion to check equality of
   two sequences of expressions.                                   *)
Fixpoint EqSeqExpr (l1 l2: seq expr) : expr :=
 match l1, l2 with
 | [::], [::] => One
 | [:: e1 & l1'], [:: e2 & l2'] =>
    And (Equal e1 e2) (EqSeqExpr l1' l2')
 | _, _ => Zero
 end.

Inductive cmd : Type :=
 | Skip : cmd
 | Assume : expr -> cmd
 | Assert : expr -> cmd
 | Assign : lvalue -> expr -> cmd
 | Seq : cmd -> cmd -> cmd
 | If : expr -> cmd -> cmd -> cmd
 | While : expr -> cmd -> cmd.

Fixpoint eq_cmd (c1 c2: cmd): bool :=
 match c1, c2 with
 | Skip, Skip => true
 | Assume e1, Assume e2 => e1==e2
 | Assert e1, Assert e2 => e1==e2
 | Assign x1 e1, Assign x2 e2 => (x1==x2) && (e1==e2)
 | Seq c11 c12, Seq c21 c22 => (eq_cmd c11 c21) && (eq_cmd c12 c22)
 | If b1 c11 c12, If b2 c21 c22 => (b1==b2) && (eq_cmd c11 c21) && (eq_cmd c12 c22)
 | While b1 c1, While b2 c2 => (b1==b2) && (eq_cmd c1 c2)
 | _, _ => false
 end.

Lemma eq_cmd_refl: forall c, eq_cmd c c.
Proof.
elim => //=.
- by move=> x e; rewrite !eq_refl.
- by move=> c1 -> c2 ->. 
- by move => b c1 -> c2 ->; rewrite eq_refl /=.
- by move => b c ->; rewrite eq_refl /=.
Qed.

Lemma cmd_eqP: Equality.axiom eq_cmd.
Proof.
move=> c1 c2; apply/(iffP idP); last first.
 move => ->; apply eq_cmd_refl.
elim: c1 c2.
- by move=> [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c2] //=.
- by move => e1 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c2] //= /eqP ->.
- by move => e1 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c2] //= /eqP ->.
- move => x1 e1 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c2] //=.
  by move => /andP [/eqP -> /eqP ->].
- move => c1 IH1 c2 IH2 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c22] //=.
  by move => /andP [/IH1 H1 /IH2 H2]; rewrite H1 H2.
- move => b1 c1 IH1 c2 IH2 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c22] //=.
  by move => /andP [/andP [/eqP -> /IH1 H1] /IH2 H2]; rewrite H1 H2.
- move => b1 c1 IH1 [|e2|e2|x2 e2|c21 c22|b2 c21 c22|b2 c22] //=.
  by move => /andP [/eqP -> /IH1 H1]; rewrite H1.
Qed.

Definition cmd_eqMixin := EqMixin cmd_eqP.
Canonical cmd_eqType := Eval hnf in EqType cmd cmd_eqMixin.

End Syntax.

Arguments Const [op_sig] _.
Arguments Var [op_sig] _.

(** * State *)
Section StateDef.

Definition upd {A:eqType} {B} (f:A->B) (x:A) (y:B) : A->B :=
 fun a => if a==x then y else f a.

(** State definition:

    [State] has two components: one that stores the contents
 of scalar variables, and one that stores the contents of 
 (unbounded) "arrays". Note that the name-spaces for scalar
 variables and arrays are distinct.
*)
Definition State := ((ident->Z)*(ident*Z->Z))%type.
Definition updVar (st:State) (v:ident) (x:Z) : State :=
 (upd st.1 v x, st.2).
Definition updArr (st:State) (a:ident) (i:Z) (x:Z) : State :=
 (st.1, upd st.2 (a,i) x).

(** Equivalence of states *)
Definition eqstate (st1 st2:State) : Prop :=
 forall id,
     st1.1 id == st2.1 id /\ (forall i, st1.2 (id,i) == st2.2 (id,i)).

Lemma eqstate_refl: forall st, eqstate st st.
Proof. by move => st id; split. Qed.

Lemma eqstate_sym: forall st1 st2, eqstate st1 st2 -> eqstate st2 st1.
Proof. 
move => st1 st2 EqS x; move: {EqS} (EqS x) => [EqSv EqSa]; split.
 by rewrite eq_sym.
by move => e; rewrite eq_sym.
Qed.

Lemma eqstate_trans: forall st1 st2 st3,
 eqstate st1 st2 -> eqstate st2 st3 -> eqstate st1 st3.
Proof.
move => st1 st2 st3 EqS12 EqS23 x.
move: {EqS12 EqS23} (EqS12 x) (EqS23 x) => [EqS12v EqS12a] [EqS23v EqS23a].
split; first by rewrite (eqP EqS12v).
by move => e; rewrite (eqP (EqS12a e)).
Qed.

(* State equality on results *)
Definition eqstateOpt (s1 s2: option State): Prop :=
 match s1, s2 with
 | None, None => True
 | Some st1, Some st2 => eqstate st1 st2
 | _, _ => False
 end.

Lemma eqstateOpt_refl: forall st, eqstateOpt st st.
Proof. by move => [st|] /=. Qed.

Lemma eqstateOpt_sym: forall st1 st2, 
 eqstateOpt st1 st2 -> eqstateOpt st2 st1.
Proof. 
move => [st1|] [st2|] //= EqS.
by apply eqstate_sym.
Qed.

Lemma eqstateOpt_trans: forall st1 st2 st3,
 eqstateOpt st1 st2 -> eqstateOpt st2 st3 -> eqstateOpt st1 st3.
Proof.
move => [st1|] [st2|] [st3|] /= EqS12 EqS23 //. 
by apply eqstate_trans with st2.
Qed.

(* State equality on results of step-indexed evaluation function *)
Definition feqstate (s1 s2: option ((option State)*seq Z)): Prop :=
 match s1, s2 with
 | None, None => True
 | Some st1, Some st2 => eqstateOpt st1.1 st2.1 /\ st1.2 = st2.2
 | _, _ => False
 end.

Lemma feqstate_refl: forall st, feqstate st st.
Proof. by move => [st|]; split => //=; apply eqstateOpt_refl. Qed.

Lemma feqstate_sym: forall st1 st2, 
 feqstate st1 st2 -> feqstate st2 st1.
Proof. 
move => [st1|] [st2|] //= [EqS EqL]; split; last by symmetry.
by apply eqstateOpt_sym.
Qed.

Lemma feqstate_trans: forall st1 st2 st3,
 feqstate st1 st2 -> feqstate st2 st3 -> feqstate st1 st3.
Proof.
move => [st1|] [st2|] [st3|] //= [Es12 El12] [Es23 El23]; split.
 by apply eqstateOpt_trans with st2.1.
by rewrite El12.
Qed.

(* State equivalence on a restricted (finite) set of variables
  Remark: for the sake of simplicity, we restrict variable restrictions
  to scalar variables
*)
Definition VarRestr:= seq ident.

Definition eqstateR (lowVar:VarRestr) (st1 st2:State) :=
 forall id,
   (id \in lowVar -> st1.1 id == st2.1 id).

Lemma eqstateR_refl: forall lowVars st, eqstateR lowVars st st.
Proof. by rewrite /eqstateR => lV st x Hx. Qed.

Lemma eqstateR_sym: forall lowVars st1 st2, 
 eqstateR lowVars st1 st2 -> eqstateR lowVars st2 st1.
Proof. 
rewrite /eqstateR => lV st1 st2 EqS x Hx.
by rewrite eq_sym; apply EqS.
Qed.

Lemma eqstateR_trans: forall lowVars st1 st2 st3,
 eqstateR lowVars st1 st2 -> eqstateR lowVars st2 st3
 -> eqstateR lowVars st1 st3.
Proof.
rewrite /eqstateR => lV st1 st2 st3 EqS12 EqS23 x Hx.
by rewrite (eqP (EqS12 _ Hx)) (eqP (EqS23 _ Hx)).
Qed.

Definition lowVars0 : VarRestr := [::].

End StateDef.

Add Parametric Relation : State eqstate
 reflexivity proved by eqstate_refl
 symmetry proved by eqstate_sym
 transitivity proved by eqstate_trans
 as eqstate_equiv.

Add Parametric Relation (lowVars:VarRestr) : State (@eqstateR lowVars)
 reflexivity proved by (@eqstateR_refl lowVars)
 symmetry proved by (@eqstateR_sym lowVars)
 transitivity proved by (@eqstateR_trans lowVars)
 as eqstateR_equiv.

Add Parametric Morphism (lowVars:VarRestr) : (eqstateR lowVars)
 with signature eqstate ==> eqstate ==> iff
 as eqstateR_morph.
Proof. 
rewrite /eqstateR => s1 s1' Es1 s2 s2' Es2.
split=> H x Hx; move: {H Es1 Es2} (H x Hx) (Es1 x) (Es2 x)
 => /eqP H [/eqP H1 _] [/eqP H2 _].
 by rewrite -H1 -H2 H.
by rewrite H1 H2 H.
Qed.

Add Parametric Relation : (option State) eqstateOpt
 reflexivity proved by eqstateOpt_refl
 symmetry proved by eqstateOpt_sym
 transitivity proved by eqstateOpt_trans
 as eqstateOpt_equiv.

Add Parametric Relation : (option ((option State)*seq Z)) feqstate
 reflexivity proved by feqstate_refl
 symmetry proved by feqstate_sym
 transitivity proved by feqstate_trans
 as feqstate_equiv.

(** * Expression Evaluation *)
Section ExprSemantics.

Variable ops : opSig.

Fixpoint eval_expr (st:State) (e:expr ops) : Z :=
 match e with
 | ValOf x => eval_lvalue st x
 | Const z => z
 | Minus e1 e2 => (eval_expr st e1 - eval_expr st e2)%Z
 | Mult e1 e2 => (eval_expr st e1 * eval_expr st e2)%Z
 | Equal e1 e2 => if (eval_expr st e1)==(eval_expr st e2) then 1%Z else 0%Z
 | Op o args => op_sem o (eval_texpr st [::] args)
 end
with eval_texpr st args {n} (x:texpr ops n) : seq Z :=
 match x with
 | t_nil => args
 | t_cons _ x l => eval_texpr st [:: eval_expr st x & args] l
 end
with eval_lvalue st (x:lvalue ops) : Z :=
 match x with
 | Var id => st.1 id
 | ArrCell id e => st.2 (id,eval_expr st e)
 end.

Lemma eval_Minus: forall st (e1 e2: expr ops),
 eval_expr st (Minus e1 e2) = eval_expr st e1 - eval_expr st e2.
Proof. by []. Qed.

Lemma eval_Mult: forall st (e1 e2: expr ops),
 eval_expr st (Mult e1 e2) = eval_expr st e1 * eval_expr st e2.
Proof. by []. Qed.

Lemma eval_Equal: forall st (e1 e2: expr ops),
 eval_expr st (Equal e1 e2)
 = if eval_expr st e1 == eval_expr st e2 then 1 else 0.
Proof. by []. Qed.

Lemma eval_tcons: forall st (e: expr ops) n (t:texpr ops n) zl,
 eval_texpr st zl (t_cons e t) = eval_texpr st [::eval_expr st e & zl] t.
Proof. by []. Qed.

Lemma eval_ArrCell: forall st a (e: expr ops),
 eval_lvalue st (ArrCell a e) = st.2 (a,eval_expr st e).
Proof. by []. Qed.

Definition isTrue_expr st (e: expr ops) := eval_expr st e != 0.

Lemma isTrue_Equal: forall st (e1 e2:expr ops),
 isTrue_expr st (Equal e1 e2)
 = (eval_expr st e1 == eval_expr st e2).
Proof.
rewrite /isTrue_expr => st e1 e2 /=.
by case: (ifP _).
Qed.

Lemma eval_Zero: forall st, eval_expr st (@Zero ops) = 0.
Proof. by []. Qed.

Lemma eval_One: forall st, eval_expr st (@One ops) = 1.
Proof. by []. Qed.

Lemma eval_IsTrue: forall st (e:expr ops),
 eval_expr st (IsTrue e) = if eval_expr st e == 0 then 0 else 1.
Proof.
move => st e.
rewrite /IsTrue /Not eval_Minus eval_One eval_Equal eval_Zero.
by case: (ifP _).
Qed.

Lemma isTrue_And: forall st (e1 e2:expr ops),
 isTrue_expr st (And e1 e2) = isTrue_expr st e1 && isTrue_expr st e2.
Proof.
move => st e1 e2.
rewrite /And /isTrue_expr eval_Mult !eval_IsTrue.
by case: (ifP _); case: (ifP _).
Qed.

Lemma isTrue_EqSeqExpr: forall st (l1 l2: seq (expr ops)),
 isTrue_expr st (EqSeqExpr l1 l2)
 <-> map (eval_expr st) l1 = map (eval_expr st) l2.
Proof.
move => st; elim => [ [|y ys] | x xs IH [|y ys] ] //=.
rewrite isTrue_And; split.
 rewrite isTrue_Equal => /andP [/eqP -> H2].
 rewrite -> IH in H2.
 by rewrite H2.
move => [H1 H2].
apply/andP; split; first by rewrite isTrue_Equal H1.
by rewrite IH.
Qed.

(** update the state for an [lvalue] *)
Definition updLValue st (l:lvalue ops) x :=
 match l with
 | Var v => updVar st v x
 | ArrCell a i => updArr st a (eval_expr st i) x
 end.

Lemma eval_expr_compat: forall st1 st2,
 eqstate st1 st2 -> forall e,
 eval_expr st1 e = eval_expr st2 e.
Proof.
move => st1 st2 EqS e; move: e st1 st2 EqS.
pose P1 e := (forall st1 st2 : State,
    eqstateOpt (Some st1) (Some st2) -> eval_expr st1 e = eval_expr st2 e).
pose P2 n (args: texpr ops n) := (forall (st1 st2 : State) zl1 zl2,
   eqstateOpt (Some st1) (Some st2) -> zl1=zl2 -> eval_texpr st1 zl1 args = eval_texpr st2 zl2 args).
pose P3 l := (forall (st1 st2 : State),
    eqstateOpt (Some st1) (Some st2) -> eval_lvalue st1 l = eval_lvalue st2 l).
apply (@expr_mixed_ind ops P1 P2 P3); unfold P1, P2, P3.
(* ValOf *) 
move => l IH st1 st2 EqSt.
by apply IH; apply EqSt.
(* Const *)
by move => z st1 st2 _ /=.
(* Minus *)
move => e1 IH1 e2 IH2 st1 st2 EqSt /=.
by rewrite (@IH1 _ st2) // (@IH2 _ st2) //.
(* Mult *)
move => e1 IH1 e2 IH2 st1 st2 EqSt /=.
by rewrite (@IH1 _ st2) // (@IH2 _ st2) //.
(* Equal *)
move => e1 IH1 e2 IH2 st1 st2 EqSt /=.
by rewrite (@IH1 _ st2) // (@IH2 _ st2) //.
(* Op *)
move => o args IH st1 st2 EqSt /=.
by rewrite (@IH _ st2 [::] [::]).
(* t_nil *)
by move => st1 st2 EqSt /=.
(* t_cons *)
move => n e IHe args IHargs st1 st2 zl1 zl2 EqSt EqZl /=.
by rewrite (@IHe _ st2) // EqZl; apply IHargs.
(* Var *)
move => v st1 st2 /= EqSt.
by move: (EqSt v) => [/eqP E _].
(* ArrCell *)
move => a i IHi st1 st2 /= EqSt.
rewrite (@IHi _ st2) //.
move: (EqSt a) => [_ E].
by rewrite (eqP (E (eval_expr st2 i))).
Qed.

Lemma updLValue_compat: forall st1 st2,
 eqstate st1 st2 -> forall l z,
 eqstate (updLValue st1 l z) (updLValue st2 l z).
Proof.
move => st1 st2 EqS [v|a e] z i; move: (EqS i) => [EqS1 EqS2].
 rewrite /= /upd /=.
 by case (i==v); split.
split => //= e'. 
 rewrite (eval_expr_compat EqS) /upd //.
by rewrite (eqP (EqS2 e')).
Qed.

(** Leakage:

  The evaluation relation is parametrised by a [leak] function that
 produces a sequence of observable events, which includes every branch
 decision taken during execution as well other (unspecified) leakage
 released during expression evaluation.
  For the sake of simplicity, we assume the leakage released on expression
 evaluation to consist itself of a sequence of integers obtained by
 evaluation of leaked expressions. Such a syntactic characterization of
 leakage allow us to obtain from free some desirable parametricity
 properties (e.g. the information leaked can, of course, depend on the
 state --- however, we cannot decide to leak or not some datum based
 on the state).
*)
Definition LeakFun := expr ops -> seq (expr ops).

Definition Leakage : eqType := [eqType of seq Z].

Definition leak_expr (lFun:LeakFun) st e : Leakage :=
 map (fun e => eval_expr st e) (lFun e).

Lemma eqleak_split: forall lFun st1 st2 e1 l1 l2,
 (leak_expr lFun st1 e1 ++ l1
  == leak_expr lFun st2 e1 ++ l2)
 = (leak_expr lFun st1 e1 == leak_expr lFun st2 e1)
   && (l1==l2).
Proof.
move => lFun st1 st2 e1 l1 l2.
by rewrite /leak_expr cat_map_eq.
Qed.

End ExprSemantics.

Add Parametric Morphism : (@Some State)
 with signature eqstate ==> eqstateOpt
 as Some_morph.
Proof. by []. Qed.

Add Parametric Morphism (ops:opSig) : (@eval_expr ops)
 with signature eqstate ==> (@eq (expr ops)) ==> (@eq Z)
 as eval_expr_morph.
Proof. by apply eval_expr_compat. Qed.

Add Parametric Morphism (ops:opSig) : (@isTrue_expr ops)
 with signature eqstate ==> (@eq (expr ops)) ==> (@eq bool)
 as isTrue_expr_morph.
Proof. by move => x y EqS e; rewrite /isTrue_expr EqS. Qed.

Add Parametric Morphism (ops:opSig) : (@updLValue ops)
 with signature
  eqstate ==> @eq (lvalue ops) ==> @eq Z ==> eqstate
 as updLValue_morph.
Proof. by apply updLValue_compat. Qed.

Add Parametric Morphism (ops:opSig) (lFun:LeakFun ops): (@leak_expr _ lFun)
 with signature eqstate ==> (@eq (expr ops)) ==> (@eq Leakage)
 as leak_expr_morph.
Proof. 
move => st1 st2 EqS e; rewrite /leak_expr.
apply eq_map => x.
by rewrite EqS.
Qed.

Section CmdEval.

Variable ops: opSig.

Variable lFun : LeakFun ops.

Inductive eval_cmd : State -> cmd ops -> Leakage -> option State -> Prop :=
 | eval_Skip: forall st,
    eval_cmd st (@Skip ops) [::] (Some st)
 | eval_AssumeT: forall st e,
    isTrue_expr st e ->
    eval_cmd st (Assume e) [::] (Some st)
 | eval_AssertF: forall st e,
    isTrue_expr st e ->
    eval_cmd st (Assert e) [::] (Some st)
 | eval_AssertT: forall st e,
    ~~(isTrue_expr st e) -> eval_cmd st (Assert e) [::] None
 | eval_Assign: forall st st' l e,
    st' = (updLValue st l (eval_expr st e)) ->
    eval_cmd st (Assign l e) (leak_expr lFun st (ValOf l)++leak_expr lFun st e)
                (Some st')
 | eval_SeqS: forall st1 st2 st3 c1 c2 l1 l2,
    eval_cmd st1 c1 l1 (Some st2) -> eval_cmd st2 c2 l2 st3 
    -> eval_cmd st1 (Seq c1 c2) (l1++l2) st3
 | eval_SeqN: forall st1 c1 c2 l1,
    eval_cmd st1 c1 l1 None -> eval_cmd st1 (Seq c1 c2) l1 None
 | eval_IfT: forall st1 st2 b c1 c2 l1,
    isTrue_expr st1 b -> eval_cmd st1 c1 l1 st2 ->
    eval_cmd st1 (If b c1 c2) (leak_expr lFun st1 b ++ (1::l1)) st2
 | eval_IfF: forall st1 st2 b c1 c2 l2,
    ~~(isTrue_expr st1 b) -> eval_cmd st1 c2 l2 st2 ->
    eval_cmd st1 (If b c1 c2) (leak_expr lFun st1 b ++ (0::l2)) st2
 | eval_WhileTS: forall st1 st2 st3 b c l1 l2,
    isTrue_expr st1 b -> 
    eval_cmd st1 c l1 (Some st2) ->
    eval_cmd st2 (While b c) l2 st3 ->
    eval_cmd st1 (While b c) (leak_expr lFun st1 b ++ 1::l1++l2) st3
 | eval_WhileTN: forall st1 b c l,
    isTrue_expr st1 b -> 
    eval_cmd st1 c l None ->
    eval_cmd st1 (While b c) (leak_expr lFun st1 b ++ 1::l) None
 | eval_WhileF: forall st b c,
    ~~(isTrue_expr st b) ->
    eval_cmd st (While b c) (leak_expr lFun st b ++ [:: 0]) (Some st).

(** Inversion lemmas *)
Lemma eval_cmd_SkipI: forall s1 l s2,
 eval_cmd s1 (@Skip ops) l s2 -> 
 s2 = (Some s1) /\ l=[::].
Proof.
move=> s1 l s2.
move: {1 3}(@Skip ops) (Logic.eq_refl (@Skip ops)) => c' E H.
by case: H E.
Qed.

Lemma eval_cmd_AssumeI: forall e s1 l s2,
 eval_cmd s1 (Assume e) l s2 -> 
 [/\ isTrue_expr s1 e, s2 = Some s1 & l=[::] ].
Proof.
move=> e s1 l s2.
move: {1 3}(Assume _) (Logic.eq_refl (Assume e)) => c' E H.
case: {c' s1 l s2} H E => //=.
by move=> s1 e' Es [<-].
Qed.

Lemma eval_cmd_AssertSI: forall e s1 l s2,
 eval_cmd s1 (Assert e) l (Some s2) -> 
 [/\ isTrue_expr s1 e, s2 = s1 & l=[::] ].
Proof.
move=> e s1 l s2.
move: {1 3}(Assert _) (Logic.eq_refl (Assert e)) => c' Ec.
move: {1 3}(Some s2) (Logic.eq_refl (Some s2)) => s' Es H.
case: {c' s' s1 s2 l} H Ec s2 Es => //=.
by move=> s1 e' Te' [<-] s' [<-].
Qed.

Lemma eval_cmd_AssertNI: forall e s1 l,
 eval_cmd s1 (Assert e) l None -> 
 [/\ ~~ isTrue_expr s1 e & l=[::] ].
Proof.
move=> e s1 l.
move: {1 3}(Assert _) (Logic.eq_refl (Assert e)) => c' Ec.
move: {1 3}None (Logic.eq_refl (@None State)) => s' Es H.
case: {c' s1 l} H Ec Es=> //=.
by move => s1 e' Te [<-] _.
Qed.

Lemma eval_cmd_AssignI: forall x e s1 l s2,
 eval_cmd s1 (Assign x e) l s2 -> 
 [/\ (s2 = Some (updLValue s1 x (eval_expr s1 e)))
     & l=leak_expr lFun s1 (ValOf x) ++ leak_expr lFun s1 e ].
Proof.
move=> x e s1 l s2.
move: {1 3}(Assign _) (Logic.eq_refl (Assign x e)) => c' Ec.
move: {1 3}(Some _) (Logic.eq_refl (Some (updLValue s1 x (eval_expr s1 e)))) => s' Es H.
case: {c' s1 s2 l} H Ec Es=> //=.
move => s1 s2 x' e' Es [<- <-] ->; split => //.
by f_equal.
Qed.

Lemma eval_cmd_SeqI: forall c1 c2 s1 l s2,
 eval_cmd s1 (Seq c1 c2) l s2 ->
 s2 = None /\ eval_cmd s1 c1 l None
 \/ exists s' l1 l2,
     [/\ eval_cmd s1 c1 l1 (Some s')
       , eval_cmd s' c2 l2 s2
       & l = l1++l2]. 
Proof.
move=> c1 c2 s1 l s2.
move: {1 3}(Seq _ _) (Logic.eq_refl (Seq c1 c2)) => c' Ec H.
case: {c' s1 s2 l} H Ec => //=.
 move=> s1 s2 s3 c1' c2' l1 l2 H1 H2 [<- <-]; right.
 by exists s2, l1, l2.
by move=> s1 c1' c2' l1 H1 [<- <-]; left.
Qed.

Lemma eval_cmd_SeqSI: forall c1 c2 s1 l s2,
 eval_cmd s1 (Seq c1 c2) l (Some s2) ->
 exists s' l1 l2, 
 [/\ eval_cmd s1 c1 l1 (Some s')
   , eval_cmd s' c2 l2 (Some s2)
   & l = l1++l2]. 
Proof.
move=> c1 c2 s1 l s2 /eval_cmd_SeqI [[Es _] // | [s' [l1' [l2' [H1 H2]]]] El].
by exists s', l1', l2'.
Qed.

Lemma eval_cmd_SeqNI: forall c1 c2 s1 l,
 eval_cmd s1 (Seq c1 c2) l None ->
 eval_cmd s1 c1 l None
 \/ exists s' l1 l2,
      [/\ eval_cmd s1 c1 l1 (Some s')
        , eval_cmd s' c2 l2 None
        & l = l1++l2]. 
Proof.
move=> c1 c2 s1 l  /eval_cmd_SeqI [[Es H1]| [s' [l1' [l2' [H1 H2]]]] El].
 by left.
by right; exists s', l1', l2'.
Qed.

Lemma eval_cmd_IfI: forall b c1 c2 s1 l s2,
 eval_cmd s1 (If b c1 c2) l s2 ->
 exists l', 
  (if isTrue_expr s1 b
  then eval_cmd s1 c1 l' s2
  else eval_cmd s1 c2 l' s2)
  /\ l = leak_expr lFun s1 b ++ (if isTrue_expr s1 b then 1 else 0) :: l'.
Proof.
move=> b c1 c2 s1 l s2.
move: {1 3}(If _ _ _) (Logic.eq_refl (If b c1 c2)) => c' Ec H.
case: {c' s1 s2 l} H Ec => //=.
 move=> s1 s2 b' c1' c2' l Tb H [E1 [E2 E3]]; subst.
 by rewrite Tb; exists l.
move=> s1 s2 b' c1' c2' l' /negPf TNb H [E1 [E2 E3]]; subst.
by exists l'; rewrite TNb.
Qed.

Lemma eval_cmd_WhileSI: forall b c s1 l s2,
 eval_cmd s1 (While b c) l (Some s2) ->
 if isTrue_expr s1 b
 then exists s' l1' l2',
        [/\ eval_cmd s1 c l1' (Some s'),
            eval_cmd s' (While b c) l2' (Some s2)
          & l = leak_expr lFun s1 b ++ 1 :: l1' ++ l2']
 else eqstate s1 s2 /\ l = leak_expr lFun s1 b ++ [:: 0].
Proof.
move=> b c s1 l s2.
move: {1 3}(While _ _) (Logic.eq_refl (While b c)) => c' Ec.
move: {1 3}(Some _) (Logic.eq_refl (Some s2)) => s' Es H.
case: {c' s' s1 s2 l} H Ec s2 Es=> //=.
 move => s1 s2 [s3|] // b' c' l1 l2 Tb H1 H2 [E1 E2]; subst.
 move=> s' [<-]; rewrite Tb.
 by exists s2, l1, l2.
move=> s1 b' c' /negPf TNb [E1 E2]; subst.
by move => s' [<-]; rewrite TNb.
Qed.

Lemma eval_cmd_WhileNI: forall b c s1 l,
 eval_cmd s1 (While b c) l None ->
 exists l',
   [/\ isTrue_expr s1 b,
       eval_cmd s1 (Seq c (While b c)) l' None
     & l = leak_expr lFun s1 b ++ 1 :: l'].
Proof.
move=> b c s1 l.
move: {1 3}(While _ _) (Logic.eq_refl (While b c)) => c' Ec.
move: {1 3}None (Logic.eq_refl (@None State)) => s' Es H.
case: {c' s' s1 l} H Ec Es=> //=.
 move => s1 s2 [s3|] // b' c' l1 l2 Tb H1 H2 [E1 E2] _; subst.
 exists (l1 ++ l2); split => //.
 by apply eval_SeqS with s2.
move => s1 b' c' l1 Tb H1 [E1 E2] _; subst.
exists l1; split => //.
by apply eval_SeqN. 
Qed.

(*
Definition bind_feval (x:option ((option State)*Leakage))
 (f: State -> option ((option State)*Leakage))
 : option ((option State)*Leakage) :=
 match x with
 | Some (Some st',l1) => match f st' with
                         | Some (x,l2) => Some (x,l1++l2)
                         | _ => None
                         end
 | _ => x
 end.

Notation "'BIND' x f" :=
 (match x with
 | Some (Some st',l1) => match f st' with
                         | Some (x,l2) => Some (x,l1++l2)
                         | _ => None
                         end
 | _ => x
 end) (at level 200).
(*  (right associativity, at level 60).*)
*)

(** ** Step-indexed evaluation function *)
Function feval_cmd (i:nat) (c:cmd ops) (st: State)
 : option ((option State)*Leakage) :=
 match i with
 | O => None
 | S i' => match c with
           | Skip => Some (Some st, [::])
           | Assume e => if isTrue_expr st e
                         then Some (Some st, [::])
                         else None
           | Assert e => if isTrue_expr st e
                         then Some (Some st, [::])
                         else Some (None, [::])
           | Assign l e => Some (Some (updLValue st l (eval_expr st e)),
                                 leak_expr lFun st (ValOf l)
                                 ++leak_expr lFun st e)
           | Seq c1 c2 => 
              match feval_cmd i' c1 st with
              | Some (Some st',l1) => match feval_cmd i' c2 st' with
                                      | Some (x,l2) => Some (x,l1++l2)
                                      | _ => None
                                      end
              | x => x
              end
(*
              bind_feval (feval_cmd i' c1 st) (feval_cmd i' c2)
*)
           | If b c1 c2 => 
              let e := isTrue_expr st b in
              match (if e then feval_cmd i' c1 st else feval_cmd i' c2 st) with
              | Some (x,l) => Some (x,leak_expr lFun st b ++ (if e then 1 else 0)::l)
              | _ => None
              end
(*
              bind_feval (Some (Some st,leak_expr lFun st b ++ [:: inl e]))
                         (if e then feval_cmd i' c1 else feval_cmd i' c2)
*)
           | While b c => 
              let e := isTrue_expr st b in
              if e
              then match feval_cmd i' (Seq c (While b c)) st with
                   | Some (x,l) => Some (x,leak_expr lFun st b ++ 1::l)
                   | _ => None
                   end
              else (Some (Some st,leak_expr lFun st b ++ [:: 0])) 
(*
              match (if e
                     then feval_cmd i' (Seq c (While b c)) st
                     else (Some (Some st,[::]))) with
              | Some (x,l) => Some (x,leak_expr lFun st b ++ (inl e)::l)
              | _ => None
*)
(*
              bind_feval (Some (Some st,leak_expr lFun st b ++ [:: inl e]))
                         (if e
                          then (feval_cmd i' (Seq c (While b c)))
                          else fun s => Some (Some s,[::]))
*)
           end
 end.

Functional Scheme feval_ind := Induction for feval_cmd Sort Prop.

Lemma feval_cmd_weak: forall n n' st c l st',
 (n <= n')%nat -> feval_cmd n c st = Some (st',l)
 -> feval_cmd n' c st = Some (st',l).
Proof.
elim => // n IH [|n'] st [|e|e|x e|c1 c2|b c1 c2|b c] l st' //=.
- move => Hn.
  case E1: (feval_cmd n c1 st) => [[[ss|] l1]|] //=.
   apply (IH n') in E1; rewrite // E1.
   case E2: (feval_cmd n c2 ss) => [[[ss'|] l2]|] //= [<- <-].
    by apply (IH n') in E2; rewrite // E2.
   by apply (IH n') in E2; rewrite // E2.
  move => [<- <-].     
  by apply (IH n') in E1; rewrite // E1.
- move => Hn.
  case: (ifP _) => Hb.
   case E1: (feval_cmd n c1 st) => [[[ss|] l1]|] //=.
    by apply (IH n') in E1; rewrite // E1.
   move => [<- <-].     
   by apply (IH n') in E1; rewrite // E1.
  case E2: (feval_cmd n c2 st) => [[[ss|] l2]|] //=.
   by apply (IH n') in E2; rewrite // E2.
  move => [<- <-].
  by apply (IH n') in E2; rewrite // E2.
- move => Hn.
  case: (ifP _) => Hb.
   case E1: (feval_cmd n (Seq c (While b c)) st) => [[[ss|] l1]|] //=.
    by apply (IH n') in E1; rewrite // E1.
   move => [<- <-].     
   by apply (IH n') in E1; rewrite // E1.
  by move => [<- <-]. 
Qed.

Lemma eval_cmd_feval: forall st c l st',
 eval_cmd st c l st' -> 
 exists n, feval_cmd n c st = Some (st',l).
Proof.
move => s1 c l s2; elim
=> [ st
   | st e Ee
   | st e Ee | st e Ee
   | st x e 
   | sta1 sta2 [sta3|] c1 c2 l1 l2 H1 IH1 H2 IH2
   | sta1 c1 c2 l1 l2 IH
   | st [st'|] b c1 c2 l1 Eb H1 IH1
   | st [st'|] b c1 c2 l1 Eb H IH
   | st st' st'' b c' l1' l2' Eb H1 IH1 H2 IH2
   | st b c' l' Eb H1 IH 
   | st b c' Eb].
- (* Skip *)
  by exists (S O).
- (* Assume *)
  exists (S 0) => //=.
  by rewrite Ee.
- (* Assert_tt *)
  exists (S 0) => //=.
  by rewrite Ee.
- (* Assert_ff *)
  exists (S 0) => //=.
  by rewrite (negPf Ee).
- (* Assign *)
  exists (S 0). 
  by rewrite H.
- (* Seq_STT *)
  move: IH1 => [n1 IH1] //.
  move: IH2 => [n2 IH2] //.
  exists (maxn n1 n2).+1 => //=.
  have Hn1: (n1 <= maxn n1 n2)%nat by apply leq_maxl.
  apply (feval_cmd_weak Hn1) in IH1; rewrite IH1.
  have Hn2: (n2 <= maxn n1 n2)%nat by apply leq_maxr.
  by apply (feval_cmd_weak Hn2) in IH2; rewrite IH2.
- (* Seq_STF *)
  move: IH1 => [n1 IH1] //.
  move: IH2 => [n2 IH2] //.
  exists (maxn n1 n2).+1 => //=.
  have Hn1: (n1 <= maxn n1 n2)%nat by apply leq_maxl.
  apply (feval_cmd_weak Hn1) in IH1; rewrite IH1.
  have Hn2: (n2 <= maxn n1 n2)%nat by apply leq_maxr.
  by apply (feval_cmd_weak Hn2) in IH2; rewrite IH2.
- (* Seq_SF *)
  move: IH => [n IH] //.
  by exists n.+1; rewrite /= IH.
- (* If_ttT *)
  move: IH1 => [n1 IH1] //.
  by exists n1.+1; rewrite /= IH1 Eb.
- (* If_ttF *)
  move: IH1 => [n1 IH1] //.
  by exists n1.+1; rewrite /= IH1 Eb.
- (* If_ffT *)
  move: IH => [n IH] //.
  by exists n.+1; rewrite /= IH (negbTE Eb).
- (* If_ffF *)
  move: IH => [n IH] //.
  by exists n.+1; rewrite /= IH (negbTE Eb).
- (* WhileTS *)
  move: IH1 => [n1 IH1] //.
  move: IH2 => [n2 IH2] //.
  exists (maxn n1 n2).+2; rewrite /= Eb.
  have Hn1: (n1 <= maxn n1 n2)%nat by apply leq_maxl.
  apply (feval_cmd_weak Hn1) in IH1; rewrite IH1.
  have Hn2: (n2 <= maxn n1 n2)%nat by apply leq_maxr.
  by apply (feval_cmd_weak Hn2) in IH2; rewrite IH2.
- (* WhileTN *)
  move: IH => [n IH] //.
  by exists n.+2; rewrite /= Eb IH.
- (* WhileF *)
  by exists 1%N; rewrite /= (negbTE Eb).
Qed.

Lemma feval_cmd_eval: forall n st c l st',
 feval_cmd n c st = Some (st',l) -> eval_cmd st c l st'.
Proof.
elim => // n IH st [|e|e|x e|c1 c2|b c1 c2|b c] l st' /=.
- by move => [<- <-]; constructor.
- by case: (ifP _) => // H [<- <-]; constructor.
- case: (ifP _) => // H [<- <-].
   by constructor.
  by constructor; apply/negPf.
- by move => [<- <-]; constructor.
- case_eq (feval_cmd n c1 st) => //.
  move => [[ss|] l1] /IH H1.
   case_eq (feval_cmd n c2 ss) => //.
   move => [[ss2|] b2] /IH H2 [<- <-];
   by econstructor; [exact H1|exact H2].
  by move => [<- <-]; constructor.
- case: (ifP _) => Hb.
   case_eq (feval_cmd n c1 st) => //.
   by move => [[ss|] l1] /IH H1 [<- <-]; constructor.
  case_eq (feval_cmd n c2 st) => //.
  move => [[ss|] l2] /IH H1 [<- <-]; constructor => //.
   by apply/negPf.
  by apply/negPf.
- case: (ifP _) => Hb.
   case_eq (feval_cmd n (Seq c (While b c)) st) => //.
   move => [[ss|] l1] /IH H1 [<- <-].
   move/eval_cmd_SeqSI: H1 => [s' [l21 [l22 [H21 H22 ->]]]].
   by econstructor; eauto.
  move/eval_cmd_SeqNI: H1 => [H1|].
   by constructor.
  move => [s' [l21 [l22 [H21 H22 ->]]]].
  by econstructor; eauto.
- move => [<- <-]; constructor => //.
  by apply/negPf.
Qed.

Lemma feval_eqstate: forall n c sa sb, 
 eqstate sa sb ->
 feqstate (feval_cmd n c sa) (feval_cmd n c sb).
Proof.
elim => // n IH [|e|e|x e|c1 c2|b c1 c2|b c] sa sb EqS //=.
- by case: (ifP _) => //=; rewrite /isTrue_expr; try rewrite -> EqS => [->].
- by case: (ifP _) => //=; rewrite /isTrue_expr; try rewrite -> EqS => [->].
- split.
   admit.
  by rewrite EqS.
- admit.
- admit.
- admit.
Qed.

Lemma feval_eqstateN: forall n c sa sb, 
 eqstate sa sb ->
 feval_cmd n c sa = None -> feval_cmd n c sb = None.
Proof.
admit.
Qed.

Lemma feval_eqstateS: forall n c sa sb sa' l, 
 eqstate sa sb ->
 feval_cmd n c sa = Some (sa',l) ->
 exists sb', feval_cmd n c sb = Some (sb',l) /\ eqstateOpt sa' sb'.
Proof.
admit.
Qed.


Lemma eval_cmd_eqstate: forall c st1 l1 st1' st2,
  eqstate st1 st2 ->
  eval_cmd st1 c l1 st1' -> 
  exists st2', eval_cmd st2 c l1 st2' /\  eqstateOpt st1' st2'.
Proof.
admit
(*
move => c st1 l st1'; elim 
=> [ st st' EqS1
   | st st' e EqS1 Ee
   | st st' e EqS1 Ee | st e Ee
   | st st' x e EqS1
   | sta1 sta2 [sta3|] c1 c2 l1 l2 H1 IH1 H2 IH2
   | sta1 c1 c2 l1 l2 IH
   | st [st'|] b c1 c2 l1 Eb H1 IH1
   | st [st'|] b c1 c2 l1 Eb H IH
   | st st' st'' b c' l1' l2' Eb H1 IH1 H2 IH2
   | st b c' l' Eb H1 IH 
   | st st' b c' Eb EqS1]  st2 [st2'|] EqS //= EqS2.
- (* Skip *)
  by constructor; rewrite -EqS -EqS2.
- (* Assume *)
  constructor. 
   by rewrite -EqS -EqS2.
  by rewrite -EqS.
- (* Assert_tt *)
  constructor. 
   by rewrite -EqS -EqS2.
  by rewrite -EqS.
- (* Assert_ff *)
  by constructor; rewrite -EqS.
- (* Assign *)
  rewrite EqS.
  by constructor; rewrite -EqS -EqS2.
- (* Seq_S *)
  apply eval_SeqS with sta2.
   by apply IH1.
  by apply IH2.
- (* Seq_S *)
  apply eval_SeqS with sta2.
   by apply IH1.
  by [].
- (* Seq_N *)
  apply eval_SeqN. 
  by apply IH.
- (* If_tt *)
  rewrite EqS; constructor.
   by rewrite -EqS.
  by apply IH1.
- (* If_tt *)
  rewrite EqS; constructor.
   by rewrite -EqS.
  by apply IH1.
- (* If_ff *)
  rewrite EqS; constructor.
   by rewrite -EqS.
  by apply IH.
- (* If_ff *)
  rewrite EqS; constructor.
   by rewrite -EqS.
  by apply IH.
- (* WhileTS *)
  rewrite EqS; eapply eval_WhileTS.
    by rewrite -EqS.
   by apply IH1 => //=.
  by apply IH2.
- (* WhileTS *)
  rewrite EqS; eapply eval_WhileTS.
    by rewrite -EqS.
   by apply IH1 => //=.
  by apply IH2.
- (* WhileTN *)
  rewrite EqS; eapply eval_WhileTN.
   by rewrite -EqS.
  by apply IH.
- (* WhileF *)
  rewrite EqS; constructor.
   by rewrite -EqS.
  by rewrite -EqS -EqS2.
*).
Qed.

(*
Lemma eval_cmd_compat: forall st1 st2,
 eqstate st1 st2 ->
 forall c l st1' st2',
  eqstateOpt st1' st2' ->
  (eval_cmd st1 c l st1' <->
   eval_cmd st2 c l st2').
Proof.
move => st1 st2 eqS c l st1' st2' eqS'; split => H.
 by apply (eval_cmd_eqstate H).
symmetry in eqS; symmetry in eqS'.
by apply (eval_cmd_eqstate H).
Qed.
*)

End CmdEval.

(*
Add Parametric Morphism (ops:opSig) (lFun:LeakFun ops): (@eval_cmd _ lFun)
 with signature
  eqstate ==> @eq (cmd ops) ==> @eq Leakage ==> eqstateOpt ==> iff
 as eval_cmd_morph.
Proof. by apply eval_cmd_compat. Qed.
*)

Section EvalProps.

Variable ops: opSig.
Variable lFun: LeakFun ops.

(** The length of leakage can only depend on the control path. Moreover,
  the control path is always leaked, which allows us to split leakages
  of secure programs...                                               *)
Lemma eval_cmd_leak_split: forall c st1 st2 st1' st2' l1 l2 l3 l4,
 eval_cmd lFun st1 c l1 (Some st1') ->
 eval_cmd lFun st2 c l2 (Some st2') -> 
 l1++l3 == l2++l4 -> (l1==l2) && (l3==l4).
Proof.
move=> c s1 s2 s1' s2' l1 l2 l3 l4 H1 H2; move: H1 s2 l2 s2' H2 l3 l4.
move: {1 3}(Some s1') (eqstateOpt_refl (Some s1')) => os Eos H1.
elim: H1 s1' Eos
=> [ sta 
   | sta e Ee
   | sta e Ee | sta e Ee
   | sta stb x e ->
   | sta stb stc ca cb la lb Ha IHa Hb IHb
   | sta c1 c2 la lb IH
   | sta stb b ca cb la Eb Ha IHa
   | sta stb b ca cb lb Eb Hb IHb
   | sta stb stc b cb la lb Eb Ha IHa Hb IHb
   | sta b cb lb Eb Ha IHa 
   | sta b cb Eb] s1' //= Eos s2 l2 s2'.
- (* skip *)
by move=> /eval_cmd_SkipI [/= EqS ->].
- (* assume *)
by move=> /eval_cmd_AssumeI [/= EqS _ ->].
- (* assertT *)
by move=> /eval_cmd_AssertSI [/= EqS _ ->].
- (* assign *)
move=> /eval_cmd_AssignI /= [EqS ->] l3 l4.
rewrite -!catA !eqleak_split => /andP [/eqP -> /andP [/eqP -> /eqP ->]].
by repeat (apply/andP; split).
- (* seq *)
move=> /eval_cmd_SeqSI //= [s' [l1' [l2' [H1 H2 ->]]]] l3 l4.
rewrite -!catA => H.
have: (la==l1') && (lb++l3 == l2' ++ l4).
 by apply IHa with stb s2 s'.
move => {H} /andP [/eqP Ela H].
have: (lb==l2') && (l3 == l4).
 by apply IHb with s1' s' s2'.
move => {H} /andP [/eqP -> /eqP ->].
by rewrite Ela; apply/andP; split.
- (* ifT *)
move=> /eval_cmd_IfI //= [l'].
case/boolP: (isTrue_expr s2 b); last first.
 move => _ [_ ->] l3 l4.
 rewrite -!catA eqleak_split => /andP [_].
 by rewrite eqE.
move=> _ [H1 ->] l3 l4.
rewrite -!catA eqleak_split => /andP [/eqP ->].
rewrite /= eqE /= => H.
have: (la==l') && (l3==l4).
 by apply IHa with s1' s2 s2'.
by move=> /andP [/eqP -> /eqP ->]; apply/andP; split.
- (* ifF *)
move=> /eval_cmd_IfI //= [l'].
case/boolP: (isTrue_expr s2 b).
 move => _ [_ ->] l3 l4.
 rewrite -!catA eqleak_split => /andP [_].
 by rewrite eqE.
move=> _ [H1 ->] l3 l4.
rewrite -!catA eqleak_split => /andP [/eqP ->].
rewrite /= eqE /= => H.
have: (lb==l') && (l3==l4).
 by apply IHb with s1' s2 s2'.
by move=> /andP [/eqP -> /eqP ->]; apply/andP; split.
- (* whileT *)
move=> /eval_cmd_WhileSI //=.
case/boolP: (isTrue_expr s2 b); last first.
 move => _ [_ ->] l3 l4.
 rewrite -!catA eqleak_split => /andP [_].
 by rewrite eqE.
move=> Eb' [sb [lb1 [lb2 [H1 H2 ->]]]] l3 l4.
rewrite -!catA eqleak_split => /andP [/eqP ->].
rewrite /= -!catA /= eqE /= => H.
have: (la==lb1) && (lb++l3==lb2++l4).
 by apply IHa with stb s2 sb => //.
move=> {H} /andP [/eqP -> H].
have: (lb==lb2) && (l3==l4).
 by apply IHb with s1' sb s2' => //.
by move=> /andP [/eqP -> /eqP ->]; apply/andP; split.
- (* whileF *)
move=> /eval_cmd_WhileSI //=.
case/boolP: (isTrue_expr s2 b).
 move => _ [sb [lb1 [lb2 [_ _ ->]]]] l3 l4.
 rewrite -!catA eqleak_split => /andP [_].
 by rewrite eqE.
move=> _ [-> ->] l3 l4.
rewrite -!catA eqleak_split => /andP [/eqP ->].
by rewrite /= eqE /= => /eqP ->; apply/andP; split.
Qed.

Lemma eval_cmd_determ: forall c st1 st2 st1' st2' l1 l2,
 eval_cmd lFun st1 c l1 st1' -> eval_cmd lFun st2 c l2 st2' -> 
 eqstate st1 st2 -> l1=l2 /\ eqstateOpt st1' st2'.
Proof.
admit (* é muito mais simples a prova por ... 
move => c st1 st2 st1' st2' l1 l2 H; elim: H st2 l2 st2'
=> [ sta stb EqSab
   | sta stb e EqSab Ee
   | sta stb e EqSab Ee | sta e Ee
   | sta stb x e EqSab
   | sta stb stc ca cb la lb Ha IHa Hb IHb
   | sta c1 c2 la lb IH
   | sta stb b ca cb la Eb Ha IHa
   | sta stb b ca cb lb Eb Hb IHb
   | sta stb stc b cb la lb Eb Ha IHa Hb IHb
   | sta b cb lb Eb Ha IHa 
   | sta stb b cb Eb EqSab] st2 l2 st2'.
- (* Skip *)
  move: st2' => [st2'|] /eval_cmd_SkipI [/= EqS <-]; split => //=.
  by rewrite -EqSab -EqS.
- (* Assume *)
  move: st2' => [st2'|] /eval_cmd_AssumeI [H /= EqS <-]; split => //=.
  by rewrite -EqSab -EqS.
- (* AssertS *)
  move: st2' => [st2'|]. 
   move=> /eval_cmd_AssertSI [H /= EqS <-]; split => //=.
   by rewrite -EqSab -EqS.
  move=> /eval_cmd_AssertNI [/negP TNb <-]; split => //=.
  by apply TNb; rewrite -H.
- (* AssertN *)
  move: st2' => [st2'|]. 
   move=> /eval_cmd_AssertSI [H /= EqS <-] EqS2; split => //=.
   by move/negP: Ee; apply; rewrite EqS2.
  move=> /eval_cmd_AssertNI [/negP TNb <-]; split => //=.
- (* Assign *)
  move: st2' => [st2'|] /eval_cmd_AssignI [//= -> ->] EqS; split => //.
   by rewrite EqS.
  by rewrite -EqS -EqSab.
- (* SeqS *)
  move=> /eval_cmd_SeqI [[H1 H2] H3|[s' [l1' [l2' [H1 H2 H3 H4]]]]]; subst.
   by move: (IHa _ _ _ H2 H3) => [_ ?].   
  move: {IHa H1} (IHa _ _ _ H1 H4) => /= [E1 EqS]; subst.
  by move: {IHb H2} (IHb _ _ _ H2 EqS) => /= [E2 EqS2]; subst.
- (* SeqN *)
  move=> /eval_cmd_SeqI [[//= H1 H2 H3]|[s' [l1' [l2' [H1 H2 H3 H4]]]]]; subst.
   by move: {IH H2} (IH _ _ _ H2 H3) => [El _].
  by move: {IH H1} (IH _ _ _ H1 H4) => [E1 ?].
- (* IfT*)
  move=> /eval_cmd_IfI [l' [H1 H2] H3].
  move: Eb H1 H2; rewrite H3 => -> H4 H2.
  move: {IHa H4} (IHa _ _ _ H4 H3) => [-> ->]; split => //.
  reflexivity.
- (* IfF *)
  move=> /eval_cmd_IfI [l' [H1 H2] H3].
  move/negPf: Eb H1 H2; rewrite H3 => -> H4 H2.
  move: {IHb H4} (IHb _ _ _ H4 H3) => [-> ->]; split => //.
  reflexivity.
- (* WhileTS *)
  move: st2' => [st2'|]. 
   move=> /eval_cmd_WhileSI; case/boolP: (isTrue_expr st2 b).
    move=> Eb' [s' [l1' [l2' [H1 H2 H3]]]] EqS.
    move: {IHa H1} (IHa _ _ _ H1 EqS) => [Ha1 /= Ha2].
    move: {IHb H2} (IHb _ _ _ H2 Ha2) => [Hb1 Hb2]; subst; split => //.
    by rewrite EqS.
   move=> Eb' [H1 H2] EqS.
   by move/negP: Eb'; elim; rewrite -EqS.
  move=> /eval_cmd_WhileNI [l' [H1]].
  move=> /eval_cmd_SeqNI [H2|[s' [l1' [l2' [H2 H3]]]]] El Es.
   by move: {IHa H2} (IHa _ _ _ H2 Es) => [_ //= ?].
  move=> EqS; move: {IHa H2} (IHa _ _ _ H2 EqS) => [El1 /= Es1].
  move: {IHb H3} (IHb _ _ _ H3 Es1) => [El2 /= Es2]; subst; split => //.
  by rewrite EqS.
- (* WhileTN *)
  move: st2' => [st2'|]. 
   move=> /eval_cmd_WhileSI; case/boolP: (isTrue_expr st2 b).
    move=> Eb' [s' [l1' [l2' [H1 H2 H3]]]] EqS.
    by move: {IHa H1} (IHa _ _ _ H1 EqS) => [Ha1 /= Ha2].
   move=> Eb' [H1 H2] EqS.
   by move/negP: Eb'; elim; rewrite -EqS.
  move=> /eval_cmd_WhileNI [l' [H1]].
  move=> /eval_cmd_SeqNI [H2|[s' [l1' [l2' [H2 H3]]]]] El Es.
   move: {IHa H2} (IHa _ _ _ H2 Es) => [El1 _]; subst; split => //.
   by rewrite Es.
  by move=> EqS; move: {IHa H2} (IHa _ _ _ H2 EqS) => [El1 /= Es1].
- (* WhileF *)
  move: st2' => [st2'|]. 
   move=> /eval_cmd_WhileSI; case/boolP: (isTrue_expr st2 b).
    move=> Eb' [s' [l1' [l2' [H1 H2 H3]]]] EqS.
    by move/negP: Eb; elim; rewrite EqS.
   move=> Eb' [H1 H2] EqS; split => //=.
    by rewrite EqS.
   by rewrite -H1 -EqS EqSab.
  move=> /eval_cmd_WhileNI [l' [H1]].
  move=> /eval_cmd_SeqNI [H2 El|[s' [l1' [l2' [H2 H3]]]] El1 El2] Es.
   by move/negP: Eb; elim; rewrite Es.
  by move/negP: Eb; elim; rewrite Es.
*).
Qed.

(** * Program Safety

  A program is [Safe] if it doesn't terminate in the error state.
*)
Definition Safe lspec (c:cmd ops) :=
 forall st st' l, eval_cmd lspec st c l st' -> st'<>None.


(** * Leakage Security (with disclosure of portion of the output state)

  A program is leakage secure if, for every pair of L-equivalent states,
 it terminates when executed on each of the two states and, whenever
 the disclosed portion of the output states agree, they necessarilly
 leak the same information.
*)
Definition leakSecure (lowInputs lowOutputs:VarRestr) (c:cmd ops) :=
 forall s1 l1 ss1,
   eval_cmd lFun s1 c l1 ss1 ->
   exists s1', ss1 = Some s1' /\ forall s2 s2' l2,
    eqstateR lowInputs s1 s2 ->
    eval_cmd lFun s2 c l2 (Some s2') ->
    eqstateR lowOutputs s1' s2' -> l1 = l2.

(** * Leakage Security (with disclosure of portion of the output state)

   An important instance of the [leakSecure] notion is when nothing on
  the output state is disclosed.
*)
Definition strict_leakSecure (lowInputs:VarRestr) (c:cmd ops) :=
  leakSecure lowInputs lowVars0 c.

End EvalProps.

