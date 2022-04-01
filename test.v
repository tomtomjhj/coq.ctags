From Coq Require Import Strings.String.

Inductive εμπτγ :=.

Definition stringly_typed : string := ". Inductive nope :=. """.

Inductive tree : Set :=
  | node : forest -> tree
with forest : Set :=
  | emptyf : forest
  | consf : tree -> forest -> forest.

Fixpoint tree_size (t:tree) {struct t} : nat :=
  match t with
  | node f => S (forest_size f)
  end
with forest_size (f:forest) {struct f} : nat :=
  match f with
  | emptyf => 0
  | consf t f' => (tree_size t + forest_size f')
  end.

Inductive inductive_with_match1 (a : match True with _ => True end) :=
  | inductive_with_match1_ctor0 : ((((True)))) -> inductive_with_match1 a
  | inductive_with_match1_ctor1 : match "with"%string with _ => True end -> inductive_with_match1 a
  | inductive_with_match1_ctor2 : (match True with _ => True end) -> inductive_with_match1 a
with inductive_with_match2 (a : match True with _ => True end) :=
  | inductive_with_match2_ctor0 : (* match *) ((((True)))) -> inductive_with_match2 a
  | inductive_with_match2_ctor1 : match True with _ => True end -> inductive_with_match2 a
  | inductive_with_match2_ctor2 : (match "end"%string with _ => True end) -> inductive_with_match2 a
  .

Ltac lazy_tac :=
  lazymatch goal with
  | |- _ => idtac (* match *)
  end.

Record R := RCtor {
  #[canonical=no] R_a :> nat; (* asdf { *)
  R_b : string := "}. ";
  R_c (a : nat) : nat -> nat
} (* aoiwejf *).

Class singleton_class := method `{implicit : nat} : nat.
(* If both record body and implicit argument are possible, Coq prefers record body.  *)
Class not_singleton_class := not_method {not_implicit : nat} (* : nat (* syntax error *) *).
