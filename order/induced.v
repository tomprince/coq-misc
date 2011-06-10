(*Require Import Morphisms.*)
Require Import abstract_algebra.
Require Import orders.

Section induced_order.
Context S O `{PartialOrder O} (P : S → O).
Global Instance: Le S := λ x y, P x ≤ P y.
Global Instance: Equiv S | 100 := λ x y, P x = P y.
Global Instance: Setoid S.
Proof.
  constructor; [intro| intros ?? | intros ???]; apply H.
Qed.
Global Instance: PartialOrder (A:=S) (≤) := {}.
Proof.
  * intros ?? H1 ?? H2.
      destruct H. (*FIXME*)
    split;
      intros H0; do 2 red in H1, H2; do 3 red;
      [ rewrite <-H1, <-H2 | rewrite H1, H2 ];
      assumption.
  * constructor; compute.
    - reflexivity.
    - intros ???;
      apply RelationClasses.PreOrder_Transitive. (*FIXME*)
  * intros ??; compute.
    apply po_antisym. (*FIXME*)
Qed.

End induced_order.
