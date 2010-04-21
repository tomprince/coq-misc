Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import abstract_algebra functors categories.

Section id_nat.
Context `{Category A} `{Category B}.
Context `{!Functor (f:A->B) f'}.

Global Instance id_transformation: NaturalTransformation (fun a => cat_id : f a ⟶ f a ).
Proof.
intros a b F. rewrite id_l, id_r. reflexivity.
Qed.

End id_nat.

Section compose_nat.
Context `{Category A} `{Category B}.
Context `{!Functor (f:A->B) f'} `{!Functor (g:A->B) g'} `{!Functor (h:A->B) h'}.
Context `{!NaturalTransformation (m:f⇛g)} `{!NaturalTransformation (n:g⇛h)}.

Global Instance compose_transformation: NaturalTransformation (fun a:A => (n a)  ◎ (m a)).
Proof.
intros a b F.
rewrite <- comp_assoc, natural, comp_assoc, natural, comp_assoc.
reflexivity.
Qed.

End compose_nat.
