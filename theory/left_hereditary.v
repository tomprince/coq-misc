Set Automatic Coercions Import.
Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra util canonical_names
   theory.categories hom_functor interfaces.functors.
Require setoids dual.

Section hered.
Context `{Category C} (c : C).
Class LeftHereditary (H: ∀ {x: C}, (x ⟶ c) → Prop) := left_hereditary : ∀ {x y:C} (f:x⟶c) (g:y⟶x), H f → H (f ◎ g).
End hered.
Implicit Arguments left_hereditary [[C] [Arrows0] [CatComp0] [c] [H] [LeftHereditary] [x] [y]].

Require Import workaround_tactics.
Section hered_functor.
Context `{Category C}.
Context {c : C}.
Context `{LH: !LeftHereditary c P}.

Definition F : C -> setoids.Object := λ x: C, setoids.object (sig (P x)) _ _.
Global Program Instance F': Fmap (Arrows0:=dual.flipA) F
  := λ (v w: C) (X: w ⟶ v),  (λ f: {f: v ⟶ c | P v f}, ((`f) ◎ X) ↾ (left_hereditary (`f) X (proj2_sig f))).
Next Obligation.
constructor; try typeclasses eauto.
intros ???. compute.
apply comp_proper; reflexivity || assumption.
Qed.

Global Instance: Functor (Arrows0:=dual.flipA) F F'.
Proof.
  constructor; try typeclasses eauto.
  * apply dual.cat.
  * constructor; try typeclasses eauto.
    repeat intro.
    do 4 red.
    simpl.
    apply comp_proper;
      reflexivity || assumption.
  * intros ?[x p][y q] Hxy.
    do 4 red in Hxy; simpl in Hxy.
    do 4 red. simpl.
    rewrite Hxy.
    apply right_identity.
  * intros. unfold fmap, F', compose.
    intros [x0?][y0?]?.
    simpl.
    do 4 red in H1; simpl in H1.
    do 2 red; simpl.
    rewrite H1.
    apply (comp_assoc y0 g f).
Qed.

Program Definition N' : F ⇛ homTo (c) := λ (a:C) (x: F a), proj1_sig (P:=P (a:C)) x.
Next Obligation.
  constructor; try typeclasses eauto.
  compute; auto.
Qed.
Global Instance: NaturalTransformation N'.
Proof.
  intros ???[][]?.
  simpl.
  unfold compose.
  do 4 red in H1.
  simpl in H1.
  compute.
  apply comp_proper; reflexivity || assumption.
Qed.

End hered_functor.

Section hered_nat.
Context `{Category C}.
Context `{!LeftHereditary c P}.
Context `{!LeftHereditary c Q}.
Context (HPQ : ∀ x f, P x f → Q x f).
Require Import extra_tactics.
Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.
Program Definition N : (F (P:=P)) ⇛ (F (P:=Q)) := λ a (x: F a), proj1_sig (P:=P a) x.
Global Instance: NaturalTransformation (C:=C) N.
Proof.
  intros ??? [][]?.
  simpl.
  unfold compose.
  apply comp_proper; reflexivity || assumption.
Qed.
End hered_nat.
