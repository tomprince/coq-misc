Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import abstract_algebra functors categories.

Hint Extern 4 => reflexivity.

Section id_nat.
Context `{Category A} `{Category B}.
Context `{!Functor (f:A->B) f'}.

Global Instance id_transformation: NaturalTransformation (fun a => cat_id : f a ⟶ f a ).
Proof with reflexivity.
intros a b F. rewrite id_l, id_r...
Qed.

End id_nat.

Section compose_nat.
Context `{Category A} `{Category B}.
Context `{!Functor (f:A->B) f'} `{!Functor (g:A->B) g'} `{!Functor (h:A->B) h'}.
Context `{!NaturalTransformation (m:f⇛g)} `{!NaturalTransformation (n:g⇛h)}.

Global Instance compose_transformation: NaturalTransformation (fun a:A => (n a)  ◎ (m a)).
Proof with reflexivity.
intros a b F.
rewrite <- comp_assoc, natural, comp_assoc, natural, comp_assoc...
Qed.

End compose_nat.
