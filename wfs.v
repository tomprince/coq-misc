Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require JMrelation.
Require Import abstract_algebra functors categories.
(* me *)
Require Import square retract.

Set Implicit Arguments.
Section stuff.

Context `(Category C).
Section ArrowClass.

Class ArrowClass (P: forall {x y: C}, (x ⟶ y) -> Prop) :=
  arrowClass: forall x y, Proper (equiv ==> equiv)%signature (P x y).

Global Instance ArrowClassIntersection `(ArrowClass P) `(ArrowClass Q) : ArrowClass (fun _ _ f => P _ _ f /\ Q _ _ f).
Proof.
  intros x y f g Hfg.
  pose (H1 x y); pose (H2 x y).
  rewrite Hfg; reflexivity.
Qed.

Global Instance SingleArrowClass `(f:a⟶b): ArrowClass (fun x y g => JMrelation.R equiv f _ equiv g).
Proof.
  intros x y g h Hgh.
  split; intro HH; destruct HH as [k ?]; apply JMrelation.relate; transitivity k; intuition symmetry; trivial.
Qed. 

End ArrowClass.

Section Factorization.
Context `{ArrowClass L}.
Context `{ArrowClass R}.

Class Factorization (x y: C) (f: x⟶y) := factorization{
  factor: C;
  left_factor: x⟶factor;
  right_factor: factor⟶y;
  left_factor_L: (L left_factor);
  right_factor_R: (R right_factor);
  factors_compose: f = right_factor◎left_factor
}.

Class WFS_factorization := wfs_factorization :> forall `(f:x⟶y), Factorization f.

End Factorization.
Implicit Arguments factor [[x][y][Factorization]].
Implicit Arguments left_factor [[x][y][Factorization]].
Implicit Arguments right_factor [[x][y][Factorization]].

Section Lift.

Class Lifting (a b x y:C) `(i:a⟶b) `(p:x⟶y) `(!Square i p (f:a⟶x) (g:b⟶y)) := lifting {
  lift: b⟶x;
  lift_left_commute: f = lift ◎ i;
  lift_right_commute: g = p ◎ lift
}.

Implicit Arguments Lifting [[a][b][x][y][Square0]].

Context `(ArrowClass L) `(ArrowClass R).
Class WFS_lift := wfs_lift :> forall (a b x y: C) (i:a⟶b) (p:x⟶y)  `(!Square i p f g) (_:L i) (_:R p), Lifting i p f g.

End Lift.

Implicit Arguments WFS_factorization.
Implicit Arguments WFS_lift.

Section Retract.
Context `{ArrowClass L}.
Class WFS_retract := wfs_retract :  forall a b a' b' (f:a⟶b) (g:a'⟶b') `{!Retract i p i' p' f g}, L f → L g.
End Retract.
Implicit Arguments WFS_retract.

Section stuff.
Context `{ArrowClass L}.
Context `{ArrowClass R}.
Context `(WFS_factorization L R).
Context `(WFS_lift L R).
Context `(WFS_retract L).
Context `(WFS_retract R).

Lemma blah : forall `(i:a⟶b), WFS_lift (fun x y f => JMrelation.R equiv i _ equiv f) R → L i.
Proof.
intros a b i lift_fR.
pose (z := factor L R i).
pose (r := right_factor L R i).
pose (l := left_factor L R i).
assert (Sq: Square i r l  cat_id).
  red; rewrite id_l; apply factors_compose.
assert (Lifting Sq).
refine (lift_fR _ _ _ _ _ _ _ _ Sq _ (right_factor_R)).
apply JMrelation.relate; reflexivity.
assert (Retract cat_id cat_id lift r l i).
split.
apply id_l. symmetry; apply lift_right_commute.
red; rewrite id_r; symmetry; apply lift_left_commute.
red; rewrite id_r; symmetry; apply factors_compose.
apply (H5 H7).
apply left_factor_L.
Qed.
