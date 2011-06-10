Set Automatic Coercions Import.
Require Import canonical_names.
Require Import abstract_algebra.
Require Import interfaces.functors.

Section induced_category.
Context `{Category C} B (F: B → C).
Instance InducedArrow: Arrows B := λ x y, F x ⟶ F y.
Global Instance: forall x y: B, Equiv (x ⟶ y) := _.
Global Instance InducedId: CatId B := λ x, cat_id : F x ⟶ F x.
Global Instance InducedComp: CatComp B := λ x y z, comp (F x) (F y) (F z).
Global Instance InducedCateogry: Category B := {}.

Global Instance: Fmap F := λ _ _,id.
Global Program Instance: Functor F _.
Solve Obligations using reflexivity.
End induced_category.

Typeclasses Transparent InducedArrow InducedId InducedComp Equiv_instance_0.
