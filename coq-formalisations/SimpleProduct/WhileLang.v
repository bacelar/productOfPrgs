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

Definition texpr_cast o1 o2 (p:o1==o2)
 : texpr (@op_arity op_sig o1) -> texpr (op_arity o2) :=
 (fun f => eq_rect o1 (fun o => texpr (op_arity o1) -> texpr (op_arity o))
                   f o2 (eqP p)) id.

(*
Definition EData := (Z*(Z+(ops op_sig)))%type.
Fixpoint finj_expr e :=
 match e with
 | ValOf x => finj_lvalue x
 | Const z => ((3,inl z), [::])
 | Minus e1 e2 => ((4,inl 0), [:: finj_expr e1; finj_expr e2])
 | Mult e1 e2 => ((5,inl 0), [:: finj_expr e1; finj_expr e2])
 | Equal e1 e2 => ((6,inl 0), [:: finj_expr e1; finj_expr e2])
 | Op o te => ((7,inr o), finj_texpr te)
 end
with finj_texpr n (te: texpr n) :=
 match te with
 | t_nil => [::]
 | t_cons _ e te' => (finj_expr e)::(finj_texpr te')
 end
with finj_lvalue x :=
 match x1, x2 with
 | Var v => [:: (1,inl (Zpos v)), [::]]
 | ArrCell a e => [:: (2, inl (Zpos a)), [:: finj_expr e]]
 end.
*)

(*
Fixpoint eq_expr e1 e2 :=
 match e1, e2 with
 | ValOf x1, ValOf x2 => eq_lvalue x1 x2
 | Const z1, Const z2 => z1==z2
 | Minus e11 e12, Minus e21 e22 => (eq_expr e11 e21) && (eq_expr e21 e22)
 | Mult e11 e12, Mult e21 e22 => (eq_expr e11 e21) && (eq_expr e21 e22)
 | Equal e11 e12, Equal e21 e22 => (eq_expr e11 e21) && (eq_expr e21 e22)
 | Op o1 te1, Op o2 te2 => (o1==o2) && (eq_texpr te1 te2)
 | _, _ => false
 end
with eq_texpr n1 n2 (te1: texpr n1) (te2: texpr n2) :=
 match te1, te2 with
 | t_nil, t_nil => true
 | t_cons _ e1 te1', t_cons _ e2 te2' => (eq_expr e1 e2) && (eq_texpr te1 te2)
 | _, _ => false
 end
with eq_lvalue x1 x2 :=
 match x1, x2 with
 | Var v1, Var v2 => v1==v2
 | ArrCell a1 e1, ArrCell a2 e2 => (a1==a2) && (eq_expr e1 e2)
 | _, _ => false
 end.
*)

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

End Syntax.

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

(* State equality *)
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

(* State equivalence on a restricted set of variables *)
Definition VarRestr:= ident -> (bool*bool).

Definition eqstateR (lowVar:VarRestr) (st1 st2:State) :=
 forall id,
   ((lowVar id).1 -> st1.1 id == st2.1 id)
   /\ ((lowVar id).2 -> forall i, st1.2 (id,i) == st2.2 (id,i)).

Lemma eqstateR_refl: forall lowVars st, eqstateR lowVars st st.
Proof. 
rewrite /eqstateR => lV st x; split.
 by case: (lV x).1.
by case: (lV x).2.
Qed.

Lemma eqstateR_sym: forall lowVars st1 st2, 
 eqstateR lowVars st1 st2 -> eqstateR lowVars st2 st1.
Proof. 
rewrite /eqstateR => lV st1 st2 EqS x.
move: {EqS} (EqS x) => [EqS1 EqS2]; split => Hx.
 by rewrite eq_sym; apply EqS1.
by move=> z; rewrite eq_sym; apply EqS2.
Qed.

Lemma eqstateR_trans: forall lowVars st1 st2 st3,
 eqstateR lowVars st1 st2 -> eqstateR lowVars st2 st3
 -> eqstateR lowVars st1 st3.
Proof.
rewrite /eqstateR => lV st1 st2 st3 EqS12 EqS23 x.
move: {EqS12 EqS23} (EqS12 x) (EqS23 x) => [EqS121 EqS122] [EqS231 EqS232].
split => Hx.
 by rewrite (eqP (EqS121 Hx)) (eqP (EqS231 Hx)).
by move=> z; rewrite (eqP (EqS122 Hx z)) (eqP (EqS232 Hx z)).
Qed.

Definition lowVars0 (i:ident) := (false,false).

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

Add Parametric Relation : (option State) eqstateOpt
 reflexivity proved by eqstateOpt_refl
 symmetry proved by eqstateOpt_sym
 transitivity proved by eqstateOpt_trans
 as eqstateOpt_equiv.

Add Parametric Morphism (lowVars:VarRestr) : (eqstateR lowVars)
 with signature eqstate ==> eqstate ==> iff
 as eqstateR_morph.
Proof. 
rewrite /eqstateR => s1 s1' Es1 s2 s2' Es2.
split=> H x; move: {H Es1 Es2} (H x) (Es1 x) (Es2 x)
=> [H1 H2] [/eqP Es11 Es12] [/eqP Es21 Es22].
 split => Hx.
  by rewrite -Es11 -Es21; apply H1.
 by move=> z; rewrite -(eqP (Es12 z)) -(eqP (Es22 z)); apply H2.
split => Hx.
 by rewrite Es11 Es21; apply H1.
by move=> z; rewrite (eqP (Es12 z)) (eqP (Es22 z)); apply H2.
Qed.

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

Definition Leakage : eqType := [eqType of seq (bool + Z)].

Definition leak_expr (lFun:LeakFun) st e : Leakage :=
 map (fun e => inr (eval_expr st e)) (lFun e).

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
apply eq_map => x; f_equal.
by rewrite EqS.
Qed.

Section CmdEval.

Variable ops: opSig.

Variable lFun : LeakFun ops.

Inductive eval_cmd : State -> cmd ops -> Leakage -> option State -> Prop :=
 | eval_Skip: forall st st',
    eqstate st st' -> eval_cmd st (@Skip ops) [::] (Some st')
 | eval_AssumeT: forall st st' e,
    eqstate st st' -> isTrue_expr st e ->
    eval_cmd st (Assume e) [::] (Some st')
 | eval_AssertF: forall st st' e,
    eqstate st st' -> isTrue_expr st e ->
    eval_cmd st (Assert e) [::] (Some st')
 | eval_AssertT: forall st e,
    ~~(isTrue_expr st e) -> eval_cmd st (Assert e) [::] None
 | eval_Assign: forall st st' l e,
    eqstate (updLValue st l (eval_expr st e)) st' ->
    eval_cmd st (Assign l e) (leak_expr lFun st (ValOf l)++leak_expr lFun st e)
                (Some st')
 | eval_SeqS: forall st1 st2 st3 c1 c2 l1 l2,
    eval_cmd st1 c1 l1 (Some st2) -> eval_cmd st2 c2 l2 st3 
    -> eval_cmd st1 (Seq c1 c2) (l1++l2) st3
 | eval_SeqN: forall st1 c1 c2 l1,
    eval_cmd st1 c1 l1 None -> eval_cmd st1 (Seq c1 c2) l1 None
 | eval_IfT: forall st1 st2 b c1 c2 l1,
    isTrue_expr st1 b -> eval_cmd st1 c1 l1 st2 ->
    eval_cmd st1 (If b c1 c2) (leak_expr lFun st1 b ++ (inl true)::l1) st2
 | eval_IfF: forall st1 st2 b c1 c2 l2,
    ~~(isTrue_expr st1 b) -> eval_cmd st1 c2 l2 st2 ->
    eval_cmd st1 (If b c1 c2) (leak_expr lFun st1 b ++ (inl false)::l2) st2
 | eval_WhileTS: forall st1 st2 st3 b c l1 l2,
    isTrue_expr st1 b -> 
    eval_cmd st1 c l1 (Some st2) ->
    eval_cmd st2 (While b c) l2 st3 ->
    eval_cmd st1 (While b c) (leak_expr lFun st1 b ++ (inl true)::l1++l2) st3
 | eval_WhileTN: forall st1 b c l,
    isTrue_expr st1 b -> 
    eval_cmd st1 c l None ->
    eval_cmd st1 (While b c) (leak_expr lFun st1 b ++ (inl true)::l) None
 | eval_WhileF: forall st st' b c,
    ~~(isTrue_expr st b) ->
    eqstate st st' ->
    eval_cmd st (While b c) (leak_expr lFun st b ++ [:: (inl false)]) (Some st').

(** Inversion lemmas *)
Lemma eval_cmd_SkipI: forall s1 l s2,
 eval_cmd s1 (@Skip ops) l s2 -> 
 eqstateOpt (Some s1) s2 /\ l=[::].
Proof.
move=> s1 l s2.
move: {1 3}(@Skip ops) (Logic.eq_refl (@Skip ops)) => c' E H.
by case: H E.
Qed.

Lemma eval_cmd_AssumeI: forall e s1 l s2,
 eval_cmd s1 (Assume e) l s2 -> 
 [/\ isTrue_expr s1 e, eqstateOpt (Some s1) s2 & l=[::] ].
Proof.
move=> e s1 l s2.
move: {1 3}(Assume _) (Logic.eq_refl (Assume e)) => c' E H.
case: {c' s1 l s2} H E => //=.
by move=> s1 s2 e' Es Ee [<-].
Qed.

Lemma eval_cmd_AssertSI: forall e s1 l s2,
 eval_cmd s1 (Assert e) l (Some s2) -> 
 [/\ isTrue_expr s1 e, eqstate s1 s2 & l=[::] ].
Proof.
move=> e s1 l s2.
change (eqstate s1 s2) with (eqstateOpt (Some s1) (Some s2)).
move: {1 3}(Assert _) (Logic.eq_refl (Assert e)) => c' Ec.
move: {1 3}(Some s2) (Logic.eq_refl (Some s2)) => s' Es H.
case: {c' s' s1 s2 l} H Ec s2 Es => //=.
by move=> s1 s2 e' Es Te' [<-] s' [<-].
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
 [/\ eqstateOpt s2 (Some (updLValue s1 x (eval_expr s1 e))) 
     & l=leak_expr lFun s1 (ValOf x) ++ leak_expr lFun s1 e ].
Proof.
move=> x e s1 l s2.
move: {1 3}(Assign _) (Logic.eq_refl (Assign x e)) => c' Ec.
move: {1 3}(Some _) (Logic.eq_refl (Some (updLValue s1 x (eval_expr s1 e)))) => s' Es H.
case: {c' s1 s2 l} H Ec Es=> //=.
move => s1 s2 x' e' Es [<- <-] ->; split => //.
by symmetry.
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
  /\ l = leak_expr lFun s1 b ++ inl (isTrue_expr s1 b) :: l'.
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
          & l = leak_expr lFun s1 b ++ inl true :: l1' ++ l2']
 else eqstate s1 s2 /\ l = leak_expr lFun s1 b ++ [:: inl false].
Proof.
move=> b c s1 l s2.
move: {1 3}(While _ _) (Logic.eq_refl (While b c)) => c' Ec.
move: {1 3}(Some _) (Logic.eq_refl (Some s2)) => s' Es H.
case: {c' s' s1 s2 l} H Ec s2 Es=> //=.
 move => s1 s2 [s3|] // b' c' l1 l2 Tb H1 H2 [E1 E2]; subst.
 move=> s' [<-]; rewrite Tb.
 by exists s2, l1, l2.
move=> s1 s2 b' c' /negPf TNb Es [E1 E2]; subst.
by move => s' [<-]; rewrite TNb.
Qed.

Lemma eval_cmd_WhileNI: forall b c s1 l,
 eval_cmd s1 (While b c) l None ->
 exists l',
   [/\ isTrue_expr s1 b,
       eval_cmd s1 (Seq c (While b c)) l' None
     & l = leak_expr lFun s1 b ++ inl true :: l'].
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

Lemma eval_cmd_eqstate: forall c st1 l st1', 
  eval_cmd st1 c l st1' -> 
  forall st2 st2', 
    eqstate st1 st2 ->
    eqstateOpt st1' st2' -> eval_cmd st2 c l st2'.
Proof.
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
Qed.

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

End CmdEval.

Add Parametric Morphism (ops:opSig) (lFun:LeakFun ops): (@eval_cmd _ lFun)
 with signature
  eqstate ==> @eq (cmd ops) ==> @eq Leakage ==> eqstateOpt ==> iff
 as eval_cmd_morph.
Proof. by apply eval_cmd_compat. Qed.


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
   | sta stb b cb Eb EqSab] s1' //= Eos s2 l2 s2'.
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
Qed.


(** * Program Safety

  A program is called [Safe] if, for every possible input state,
 it terminates in a non-error state
*)
Definition Safe (P:State -> Prop) (c:cmd ops) :=
 forall st, P st -> exists st' l, eval_cmd lFun st c l (Some st').

Definition assertionCmd (c:cmd ops) : bool :=
 match c with
 | Assume e | Assert e => true
 | _ => false
 end.

(** [unsafe] removes all [Assert] and [Assume] instructions from
   a program. *)
Fixpoint unsafe (c:cmd ops) : cmd ops :=
 match c with
 | Skip => @Skip ops
 | Assume e => @Skip ops
 | Assert e => @Skip ops
 | Assign x e => Assign x e
 | Seq c1 c2 => if assertionCmd c1
                then unsafe c2
                else if assertionCmd c2
                     then unsafe c1
                     else Seq (unsafe c1) (unsafe c2)
 | If b c1 c2 => If b (unsafe c1) (unsafe c2)
 | While b c => While b (unsafe c)
 end.

Lemma eval_cmd_unsafe: forall st1 c l st2,
 eval_cmd lFun st1 c l (Some st2) -> eval_cmd lFun st1 (unsafe c) l (Some st2).
Proof.
move => st1 c l st2.
move: {1 3}(Some st2) (Logic.eq_refl (Some st2)) => s Es H.
elim: H st2 Es => {st1 c l s}
   [ st st' EqS1
   | st st' e EqS1 Ee
   | st st' e EqS1 Ee | st e Ee
   | st st' x e EqS1 (* stb1 stb2  *)
   | sta1 sta2 [sta3|] c1 c2 l1 l2 H1 IH1 H2 IH2
   | sta1 c1 c2 l1 l2 IH
   | st [st'|] b c1 c2 l1 Eb H1 IH1
   | st [st'|] b c1 c2 l1 Eb H IH
   | st st' st'' b c' l1' l2' Eb H1 IH1 H2 IH2
   | st b c' l' Eb H1 IH 
   | st st' b c' Eb EqS1] //= st2 [Es]; (discriminate Es|| subst).
- (* Skip *)
by apply eval_Skip.
- (* Assume *)
by apply eval_Skip.
- (* Assert *)
by apply eval_Skip.
- (* Assign *)
by apply eval_Assign.
- (* SeqS *)
case: (ifP _).
 move: c1 H1 IH1 => [|e|e|? ?|? ?|? ? ?|? ?] //= H1 IH1 _. 
  move: H1 H2 IH2 => /eval_cmd_AssumeI [Eb /= Es El] H2 IH2.
  by rewrite El /= Es; apply IH2.
 move: H1 H2 IH2 => /eval_cmd_AssertSI [Eb /= Es El] H2 IH2.
 by rewrite El /= Es; apply IH2.
move => _; case: (ifP _).
 move: c2 H2 IH2 => [|e|e|? ?|? ?|? ? ?|? ?] //= H2 IH2 _. 
  move: H2 H1 IH1 => /eval_cmd_AssumeI [Eb /= Es El] H1 IH1.
  by rewrite El /= -Es cats0; apply IH1.
 move: H2 H1 IH1 => /eval_cmd_AssertSI [Eb /= Es ->] H1 IH1.
 by rewrite /= -Es cats0; apply IH1.
move => _; apply eval_SeqS with sta2.
 by apply IH1.
by apply IH2.
- (* IfT *)
simpl; apply eval_IfT => //.
by apply IH1.
- (* IfF *)
simpl; apply eval_IfF => //.
by apply IH.
- (* WhileT *)
apply eval_WhileTS with st' => //.
 by apply IH1 => //. 
by apply IH2.
- (* WhileF *)
by apply eval_WhileF.
Qed.

(** * Leakage Security (with disclosure of portion of the output state)

  A program is leakage secure if, for every pair of L-equivalent states,
 it terminates when executed on each of the two states and, whenever
 the disclosed portion of the output states agree, they necessarilly
 leak the same information.
*)
Definition leakSecure (lowInputs lowOutputs:VarRestr) (c:cmd ops) :=
 forall s1 s2, eqstateR lowInputs s1 s2 ->
  exists s1' s2' l1 l2,
   eval_cmd lFun s1 c l1 (Some s1')
   /\ eval_cmd lFun s2 c l2 (Some s2')
   /\ (eqstateR lowOutputs s1' s2' -> l1=l2).

(** * Leakage Security (with disclosure of portion of the output state)

   An important instance of the [leakSecure] notion is when nothing on
  the output state is disclosed.
*)
Definition strict_leakSecure (lowInputs:VarRestr) (c:cmd ops) :=
  leakSecure lowInputs lowVars0 c.

End EvalProps.

