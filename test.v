From Coq Require Import Strings.String.

Inductive εμπτγ :=.

Definition stringly_typed : string := ". Inductive nope :=. """.

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
