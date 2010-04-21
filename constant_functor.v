Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import categories abstract_algebra functors.

Set Automatic Introduction.

Section constant_functor.
Context `{Category A} `{Category B}.
Context (b:B).

Definition F : A -> B := fun _ => b.
Global Instance: Fmap F := fun _ _ _ => cat_id.

Global Instance: forall a a':A, Setoid_Morphism (fmap F:(a ⟶ a') -> (F a ⟶ F a')).
Proof.
  intros; constructor; try apply _.
  intros ? ? ?; reflexivity.
Qed.

Let preserves_id' : forall a:A, fmap F (cat_id:a⟶a) = cat_id.
Proof. reflexivity. Qed.

Let preserves_comp' : forall (a' a'' : A) (f:a'⟶a'') (a:A) (g:a⟶a'),
  fmap F (f ◎ g) = fmap F f ◎ fmap F f.
Proof. intros; rewrite <- id_l; reflexivity. Qed.

Global Program Instance ConstantFunctor : Functor (fun _ => b) (fun _ _ _ => cat_id) := {
  preserves_id := preserves_id';
  preserves_comp := preserves_comp'
}.

End constant_functor.

Section constant_transformation.
Context `{Category A} `{Category J}.
Context {a a': A}.

Global Instance constant_transformation {f:a⟶a'} : NaturalTransformation (fun j:J => f).
Proof with reflexivity.
  intros j k alpha. unfold fmap, Fmap_instance_0; rewrite id_l, id_r...
Qed.

End constant_transformation.

