Set Automatic Coercions Import.
Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra util canonical_names
   theory.categories hom_functor functors.
Require setoids dual.
(* me *)

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
Definition F x := setoids.object (sig (P x)) _ _.
(* CatComp0 is unfold due to a bug *)
Global Program Instance Fmap': Fmap (Arrows0:=dual.flipA) F
  := λ v w (X: w ⟶ v),  (λ f: {f: v ⟶ c | P v f}, (CatComp0 _ _ _ (`f) X) ↾ (left_hereditary (`f) X (proj2_sig f))).
Next Obligation.
constructor; try typeclasses eauto.
intros ???. compute.
apply comp_proper; reflexivity || assumption.
Qed.

Instance: ∀ a b, Setoid_Morphism (Fmap' a b) := {}. (*FIXME?*)
Proof.
  repeat intro.
  do 4 red.
  simpl.
  fold (@comp _ _ CatComp0 b a c).
  apply (comp_proper (CatComp0:=CatComp0) _ _ _ (`x0) (`y0) H2 x y H1 );
  reflexivity || assumption.
Qed.
Global Instance: Functor (Arrows0:=dual.flipA) F Fmap'.
Proof.
  constructor; try typeclasses eauto.
  * apply dual.cat.
  * intros ?[x p][y q] Hxy.
    do 4 red in Hxy; simpl in Hxy.
    compute.
    rewrite Hxy.
    apply right_identity.
  * repeat intro. compute. do 4 red in H1; simpl in H1.
    rewrite H1. apply comp_assoc.
Qed.
Program Definition N'' := λ a (x: F a), proj1_sig (P:=P a) x.
Program Definition N' : (F:forall _: C, _) ⇛ (homFrom (H0:=dual.cat) (c:C)) := λ (a:C) (x: F a), proj1_sig (P:=P (a:C)) x.
Next Obligation.
  constructor; try typeclasses eauto.
  compute; auto.
Qed.
Global Instance: NaturalTransformation (Arrows0:=@dual.flipA C Arrows0) (Ga:=hom_functor.Fmap_instance_0 (c:C)) N'.
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
Global Instance: NaturalTransformation (C:=C) (Arrows0:=dual.flipA) N.
Proof.
  intros ??? [][]?.
  simpl.
  unfold compose.
  apply comp_proper; reflexivity || assumption.
Qed.
End hered_nat.
