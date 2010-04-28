Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra interfaces.functors theory.categories.

Set Automatic Introduction.

Section Square.

Context `{Category C}.

Class Square {a b x y: C} (i: a⟶b) (p: x⟶y) (f: a⟶x) (g: b⟶y) := square : g◎i = p◎f.

Section comp_square.
Context `{Square a b u v i h f g} `{Square u v x y h p f' g'}.
Global Instance: Square i p (f'◎f) (g'◎g).
Proof.
red.
rewrite <- comp_assoc; hyp_rewrite.
repeat rewrite comp_assoc; hyp_rewrite.
reflexivity.
Qed.
End comp_square.
Section id_square.
Context `{i:a⟶b}.
Global Instance: Square i i cat_id cat_id.
Proof. red; rewrite id_l, id_r; reflexivity. Qed.
End id_square.

End Square.