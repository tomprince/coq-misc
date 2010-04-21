Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import categories abstract_algebra functors.

Section unit_category.

Global Instance: Arrows unit := fun _ _ => unit.
Global Instance: CatId unit := fun _ => tt.
Global Instance: CatComp unit := fun _ _ _ _ _ => tt.
Section e.
Context (x y: unit).
Global Instance: Equiv (x⟶y) := eq.
Global Instance: Setoid (x⟶y).
End e.
Global Instance: Category unit.
Proof with reflexivity.
 constructor; compute; intros; try apply _; try case a...
Qed.

End unit_category.