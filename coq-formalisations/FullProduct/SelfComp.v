Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq tuple fintype.
Require Import ZArith zint.
Require Export Setoid Relation_Definitions.

Require Import WhileLang TrfState.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Definition ident := positive.

Open Scope Z_scope.

Definition okSC_idx : Z := (-1).
Definition clSC_idx : Z := (-2).
Definition crSC_idx : Z := (-3).

Definition okSC (s:trfState) : Z := sc s (-1).
Definition clSC (s:trfState) : Z := sc s (-2).
Definition crSC (s:trfState) : Z := sc s (-3).
Definition leakSC (s:trfState) (i:Z) : Z := sc s i.

Section SCtrf.

Variable ops: opSig.

Record LeakSpec :=
 { lFun :> @LeakFun ops
 ; preleak: expr ops -> seq (expr ops)
 ; preleak_ren: forall f e,
     preleak (ren_expr f e) = map (ren_expr f) (preleak e)
 ; preleak_prod: forall s1 s2 e,
     (leak_expr preleak s1 e == leak_expr preleak s2 e)
     = (leak_expr lFun s1 e == leak_expr lFun s2 e)
 }.

Variable lspec: LeakSpec.

Definition ok_lvalue: lvalue ops := Var xH.
Definition okSC_lvalue := ArrCell xH (@Const ops okSC_idx).
Definition clSC_lvalue := ArrCell xH (@Const ops clSC_idx).
Definition crSC_lvalue := ArrCell xH (@Const ops crSC_idx).
Definition leakSC_lvalue (e: expr ops) : lvalue ops := ArrCell xH e.
Definition ok_expr: expr ops := ValOf ok_lvalue.
Definition okSC_expr: expr ops := ValOf okSC_lvalue.
Definition clSC_expr: expr ops := ValOf clSC_lvalue.
Definition crSC_expr: expr ops := ValOf crSC_lvalue.
Definition leakSC_expr (e: expr ops) : expr ops := ValOf (leakSC_lvalue e).

Definition initSC: cmd ops :=
 Seq (Assign okSC_lvalue (Const 1))
     (Seq (Assign clSC_lvalue (Const 0))
          (Assign crSC_lvalue (Const 0))).

Definition okSC_upd (e: expr ops) : cmd ops :=
 Assign okSC_lvalue (And okSC_expr e).
Definition clSC_inc : cmd ops :=
 Assign clSC_lvalue (Minus clSC_expr (Const (-1))).
Definition crSC_inc : cmd ops :=
 Assign crSC_lvalue (Minus crSC_expr (Const (-1))).


(** registers the (pre)leakage of an expression *)

Definition regVal (e: expr ops) : cmd ops :=
 Seq (Assign (leakSC_lvalue clSC_expr) e) clSC_inc.

(** checks the (pre)leakage of an expression against registered one *)

Definition chkVal (e: expr ops) : cmd ops :=
 Seq (okSC_upd (Equal (leakSC_expr crSC_expr) e)) crSC_inc.

Fixpoint procLeak (side:bool) (l: seq (expr ops)) : cmd ops :=
 match l, side with
 | [::], _ => @Skip ops
 | e::es, false => Seq (regVal e) (procLeak side es)
 | e::es, true => Seq (chkVal e) (procLeak side es)
 end.

Fixpoint mirror (side:bool) (c: cmd ops) {struct c} : cmd ops :=
 match c with
 | Skip => @Skip ops
 | Assert e => Assert (ren_expr side e)
 | Assume e => Assume (ren_expr side e)
 | Assign x e => Seq (Seq (procLeak side (preleak lspec (ren_expr side (ValOf x))))
                          (procLeak side (preleak lspec (ren_expr side e))))
                     (Assign (ren_lvalue side x) (ren_expr side e))
 | Seq c1 c2 => Seq (mirror side c1) (mirror side c2)
 | If b c1 c2 => Seq (Seq (procLeak side (preleak lspec (ren_expr side b)))
                          (procLeak side [:: IsTrue (ren_expr side b)]))
                     (If (ren_expr side b) (mirror side c1) (mirror side c2))
 | While b c1 =>
    Seq (Seq (procLeak side (preleak lspec (ren_expr side b)))
             (procLeak side [:: IsTrue (ren_expr side b)]))
        (While (ren_expr side b) 
               (Seq (mirror side c1)
                    (Seq (procLeak side (preleak lspec (ren_expr side b)))
                         (procLeak side [:: IsTrue (ren_expr side b)]))))
 end.
                 
Definition selfComp (c: cmd ops) : cmd ops :=
 Seq (Seq initSC (Seq (mirror false c) (mirror true c))) 
     (okSC_upd (Equal clSC_expr crSC_expr)).

Fixpoint matchLeak side (st:trfState) (start:Z) (l: seq Z) :=
 match l with
 | [::] => start == (if side then crSC st else clSC st)
 | (x::xs) => (x==leakSC st start) && (matchLeak side st (start+1) xs)
 end.

Inductive mirror1_spec : seq Z -> trfState -> trfState -> Prop :=
 | mirror1_nil: forall st, mirror1_spec [::] st st
 | mirror1_cons: forall x xs st st',
     mirror1_spec xs (mkTrfSt (ok st) (upd (upd (leakSC st) (clSC st) x) 
                                           clSC_idx (clSC st + 1))) st' ->
     mirror1_spec (x::xs) st st'.

Inductive mirror2_spec : seq Z -> trfState -> trfState -> Prop :=
 | mirror2_nil: forall st, mirror2_spec [::] st st
 | mirror2_cons: forall x xs st st',
     mirror2_spec xs (mkTrfSt (ok st)
                              (upd (upd (leakSC st) okSC_idx
                                        (if x==leakSC st crSC_idx
                                         then okSC st
                                         else 0))
                                   crSC_idx (crSC st + 1))) st' ->
     mirror2_spec (x::xs) st st'.

(*
mirror1_spec_cat:
mirror1_spec l1 st1 st2 -> mirror1_spec l2 st2 st3 ->
mirror1_spec (l1++l2) st1 st3.

procLeak1_spec:

exists ll,
 eval_cmd lspec (joinState (s1,s2,st))
   (procLeak false (preleak lspec (ren_expr false e)))
   ll (joinState (s1,s2,updLeakL st (leak_expr lspec (ren_expr false e))))
                        ========



Fixpoint updLeakL st l :=
 match l with
 | [::] => st
 | (x::xs) =>
    updLeakL (mkTrfSt (ok st) (upd (upd (leakSC st) (clSC st) x) 
                                   clSC_idx (clSC st + 1)))
             xs
 end.
*)

Lemma mirror1_sound: forall c s1 s2 st l1 s1',
 eval_cmd lspec s1 c l1 (Some s1') ->
 exists ll st',
  eval_cmd lspec (joinState (s1,s2,st)) (mirror false c) ll 
                 (Some (joinState (s1',s2,st')))
  /\ mirror1_spec l1 st st'.
Proof.
move => c s1 s2 st l1 s1' /eval_cmd_feval [n H].
elim: n s1 s1' l1 c H => //.
move => n IH s1 s1' l1 [|e|e|x e|c1 c2|b c1 c2|b c] /=.
- (* Skip *)
  admit.
- (* Assume *)
  admit.
- (* Assert *)
  admit.
- (* Assign *)
  move => [<- <-].
  admit.
- (* Seq *)
  admit.
- (* If *)
  admit.
- (* While *)
  admit.
Qed.

Lemma mirror1_complete: forall c s1 s2 st l1 ll s',
 eval_cmd lspec (joinState (s1,s2,st)) (mirror false c) ll 
                (Some s') ->
 mirror1_spec l1 st (splitState s').2 ->
 eval_cmd lspec s1 c l1 (Some (splitState s').1.1).
Proof.
admit (*
move => c s1 s2 st l1 s1' /eval_cmd_feval [n H].
elim: n s1 s1' l1 c H => //.
move => n IH s1 s1' l1 [|e|e|x e|c1 c2|b c1 c2|b c] /=.
- (* Skip *)
  admit.
- (* Assume *)
  admit.
- (* Assert *)
  admit.
- (* Assign *)
  move => [<- <-].
  admit.
- (* Seq *)
  admit.
- (* If *)
  admit.
- (* While *)
  admit.
*).
Qed.

Lemma mirror2_sound: forall c s1 s2 st l2 s2',
 eval_cmd lspec s2 c l2 (Some s2') ->
 exists ll st',
  eval_cmd lspec (joinState (s1,s2,st)) (mirror true c) ll 
                 (Some (joinState (s1,s2',st')))
  /\ mirror2_spec l2 st st'.
Proof.
move => c s1 s2 st l2 s2' /eval_cmd_feval [n H].
elim: n s2 s2' l2 c H => //.
move => n IH s2 s2' l2 [|e|e|x e|c1 c2|b c1 c2|b c] /=.
- (* Skip *)
  admit.
- (* Assume *)
  admit.
- (* Assert *)
  admit.
- (* Assign *)
  move => [<- <-].
  admit.
- (* Seq *)
  admit.
- (* If *)
  admit.
- (* While *)
  admit.
Qed.

Lemma mirror2_complete: forall c s1 s2 st l2 ll s',
 eval_cmd lspec (joinState (s1,s2,st)) (mirror true c) ll 
                (Some s') ->
 mirror2_spec l2 st (splitState s').2 ->
 eval_cmd lspec s2 c l2 (Some (splitState s').1.2).
Proof.
admit (*
move => c s1 s2 st l1 s1' /eval_cmd_feval [n H].
elim: n s1 s1' l1 c H => //.
move => n IH s1 s1' l1 [|e|e|x e|c1 c2|b c1 c2|b c] /=.
- (* Skip *)
  admit.
- (* Assume *)
  admit.
- (* Assert *)
  admit.
- (* Assign *)
  move => [<- <-].
  admit.
- (* Seq *)
  admit.
- (* If *)
  admit.
- (* While *)
  admit.
*).
Qed.

Theorem selfComp_sound1':
 forall n (c:cmd ops) ts (s1 s1' s2 s2': State) l1 l2,
 feval_cmd lspec n c s1 = Some (Some s1',l1) ->
 feval_cmd lspec n c s2 = Some (Some s2',l2) ->
 exists s' l',
  [/\ eval_cmd lspec (joinState (s1,s2,ts)) (selfComp c) l'
                     (Some s'),
      eqstate s1' (splitState s').1.1
    & eqstate s2' (splitState s').1.2 ].
Proof.
elim => //= n IH.
move => [|e|e|x e|c1 c2|b c1 c2|b c] ts s1 s1' s2 s2' l1 l2 /=.
- move=> [<- El1] [<- El2]; rewrite /selfComp.
  admit.
- admit.
- admit.
- admit.
- admit.
- admit.
- admit.
Qed.

Theorem selfComp_sound1:
 forall (c:cmd ops) ts (s1 s1' s2 s2': State) l1 l2,
 eval_cmd lspec s1 c l1 (Some s1') ->
 eval_cmd lspec s2 c l2 (Some s2') ->
 exists s' l',
  [/\ eval_cmd lspec (joinState (s1,s2,ts)) (selfComp c) l'
                     (Some s'),
      eqstate s1' (splitState s').1.1
    & eqstate s2' (splitState s').1.2 ].
Proof.
rewrite /selfComp => c ts s1 s1' s2 s2' l1 l2
 /eval_cmd_feval [n1 H1] /eval_cmd_feval [n2 H2].
apply selfComp_sound1' with (maxn n1 n2) l1 l2.
 apply feval_cmd_weak with n1 => //.
 by apply leq_maxl.
apply feval_cmd_weak with n2 => //.
by apply leq_maxr.
Qed.

Theorem selfComp_complete:
 forall (c:cmd ops) ts1 (s11 s12 s2: State) l1 l2 l',
 eval_cmd lspec (joinState (s11,s12,ts1)) (selfComp c) l' (Some s2) ->
 [/\ eval_cmd lspec s11 c l1 (Some (splitState s2).1.1),
     eval_cmd lspec s12 c l2 (Some (splitState s2).1.2)
   & l1==l2 = (eval_expr s2 okSC_expr != 0)].
Admitted.

Theorem selfComp_sound2:
 forall (c:cmd ops) ts ts' (s1 s1' s2 s2': State) l1 l2 l',
 eval_cmd lspec s1 c l1 (Some s1') ->
 eval_cmd lspec s2 c l2 (Some s2') ->
 eval_cmd lspec (joinState (s1,s2,ts)) (selfComp c) l'
                (Some (joinState (s1',s2',ts'))) ->
 l1==l2 = (eval_expr (joinState (s1',s2',ts')) okSC_expr != 0).
Proof.
move=> c ts ts' s1 s1' s2 s2' l1 l2 ll H1 H2
 /eval_cmd_feval [n H].
move: (selfComp_sound1 ts H1 H2) => [s' [l' [HH Es1 Es2]]].
move: (HH).
apply selfComp_complete with (l1:=l1) (l2:=l2) in HH.
move: HH => [HH1 HH2 HH3] HH.
admit (* determinism *).
Qed.

Theorem selfComp_imgN:
 forall (c:cmd ops) s ll,
   eval_cmd lspec s (selfComp c) ll None -> 
   (exists l1, eval_cmd lspec (splitState s).1.1 c l1 None)
   \/ (exists l2, eval_cmd lspec (splitState s).1.2 c l2 None).
Proof.
rewrite /selfComp => c s ll 
 /eval_cmd_SeqNI [/eval_cmd_SeqNI [H|H]|[s' [l1 [l2 [H1 H2]]]]];
 last first.
  admit (* absurd H2 *).
 admit (* main case *).
admit (* absurd H *).
Qed.

End SCtrf.


Arguments ok_lvalue [ops].
Arguments okSC_lvalue [ops].
Arguments clSC_lvalue [ops].
Arguments crSC_lvalue [ops].
Arguments leakSC_lvalue [ops] _.
Arguments ok_expr [ops].
Arguments okSC_expr [ops].
Arguments clSC_expr [ops].
Arguments crSC_expr [ops].
Arguments leakSC_expr [ops] _.
