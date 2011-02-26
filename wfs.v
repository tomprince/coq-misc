Require Import
    Morphisms RelationClasses Equivalence Setoid
    abstract_algebra functors categories square
    extra_tactics.
Require JMrelation dual.

(* me *)
Require Import retract.

Set Implicit Arguments.

Section ArrowClass.
Context `{Category C}.

Class ArrowClass (P: forall {x y: C}, (x ⟶ y) -> Prop) :=
  arrowClass:> forall x y, Proper (equiv ==> equiv)%signature (@P x y).

Global Instance ArrowClassIntersection `(ArrowClass P) `(ArrowClass Q) : ArrowClass (fun _ _ f => P _ _ f /\ Q _ _ f).
Proof.
  intros x y ???. hyp_rewrite; reflexivity.
Qed.

Global Instance SingleArrowClass `(f:a⟶b): ArrowClass (fun x y g => JMrelation.R equiv f _ equiv g).
Proof.
  intros ?????.
  split; intro HH; destruct HH as [k ?]; apply JMrelation.relate; transitivity k; intuition symmetry; trivial.
Qed.

End ArrowClass.

Section moreArrowClass.
Context `{Category C}.
Context `{!ArrowClass P}.
Definition dualP := fun x y (f:dual.flipA x y) => P f.
Global Instance DualArrowClass: ArrowClass dualP.
Proof. intros ???; hyp_apply; hyp_rewrite; reflexivity. Qed.
End moreArrowClass.
Implicit Arguments DualArrowClass [[C][Arrows0][H][ArrowClass0]].
Implicit Arguments dualP [[C][Arrows0]].

Section Factorization.
Context `{Category C}.
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.

Class Factorization (x y: C) (f: x⟶y) := factorization{
  factor: C;
  left_factor: x⟶factor;
  right_factor: factor⟶y;
  left_factor_L: (L left_factor);
  right_factor_R: (R right_factor);
  factors_compose: f = right_factor◎left_factor
}.

Class WFS_factorization := wfs_factorization :> forall {x y} (f:x⟶y), Factorization f.

End Factorization.
Implicit Arguments factorization [[C][Arrows0][H][CatComp0][x][y]].
Implicit Arguments factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments left_factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments right_factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments factors_compose [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments WFS_factorization [[C][Arrows0][H][CatComp0]].
Section moreFactorization.
Context `{Category C}.
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.
Context `{!WFS_factorization L R}.
Global Instance: WFS_factorization (dualP R) (dualP L).
Proof. intros ?? f. do 3 red in f.
apply (factorization (dualP R) (dualP L) f (factor L R f) (right_factor L R f) (left_factor L R f)).
- apply right_factor_R.
- apply left_factor_L.
- apply (factors_compose L R f).
Qed.

End moreFactorization.

Section Lift.
Context `{Category C}.
Class Lifting (a b x y:C) `(i:a⟶b) `(p:x⟶y) `(!Square i p (f:a⟶x) (g:b⟶y)) := lifting {
  lift: b⟶x;
  lift_left_commute: f = lift ◎ i;
  lift_right_commute: g = p ◎ lift
}.

Implicit Arguments Lifting [[a][b][x][y][Square0]].

Context `(!ArrowClass L) `(!ArrowClass R).
Class WFS_lift := wfs_lift :> forall (a b x y: C) (i:a⟶b) (p:x⟶y)  `(!Square i p f g) (_:L i) (_:R p), Lifting i p f g.

End Lift.
Implicit Arguments lift [[C][Arrows0][H][CatComp0][a][b][x][y][i][p][f][g][Lifting]].
Implicit Arguments lift_left_commute [[C][Arrows0][H][CatComp0][a][b][x][y][i][p][f][g][Lifting]].
Implicit Arguments lift_right_commute [[C][Arrows0][H][CatComp0][a][b][x][y][i][p][f][g][Lifting]].
Section moreLift.
Context `{Category C}.
Context `(!ArrowClass L) `(!ArrowClass R).
Context `{!WFS_lift  (L:=L) (R:=R)}.
Global Instance Dual_WFS_lift: WFS_lift (Arrows0:=dual.flipA) (L:=dualP R) (R:=dualP L).
Proof.
repeat intro.
do 3 red in i, p, f, g.
assert (Sq:Square p i g f) by
  (red; hyp_rewrite; reflexivity).
assert (Lifting Sq) by
  (apply wfs_lift; hyp_apply).
eapply lifting; compute.
instantiate (1:=lift Sq).
- apply lift_right_commute.
- apply lift_left_commute.
Qed.
End moreLift.

Section Retract.
Context `{Category C}.
Context `{!ArrowClass P}.
Class WFS_retract := wfs_retract : forall a b a' b' (f:a⟶b) (g:a'⟶b') `{!Retract i p i' p' f g}, P f → P g.
End Retract.
Section moreRetract.
Context `{Category C}.
Context `{!ArrowClass P}.
Context `{!WFS_retract (P:=P)}.
Global Instance: WFS_retract (P:=dualP P).
Proof.
repeat intro.
red. do 3 red in f, g, i, p, i', p'.
eapply wfs_retract.
- eapply retract; repeat hyp_apply.
- hyp_apply.
Qed.
End moreRetract.

Section stuff.
Context `{Category C}.
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.
Context `(!WFS_factorization L R).
Context `(!WFS_lift (L:=L) (R:=R)).
Context `(!WFS_retract (P:=L)).
Context `(!WFS_retract (P:=R)).

Lemma wfs_L_retract_closed : forall `(i:a⟶b), WFS_lift (L:=(fun x y f => JMrelation.R equiv i _ equiv f)) (R:=R) → L i.
Proof.
intros a b i lift_fR.
pose (r := right_factor L R i).
pose (l := left_factor L R i).
assert (Sq: Square i r l cat_id) by
  (red; rewrite left_identity; apply factors_compose).
assert (Lifting Sq) by
  (refine (lift_fR _ _ _ _ _ _ _ _ Sq _ (right_factor_R));
  apply JMrelation.relate; reflexivity).
eapply wfs_retract.
- split.
 + apply left_identity.
 + symmetry; apply lift_right_commute.
 + red; rewrite right_identity; symmetry; apply lift_left_commute.
 + red; rewrite right_identity; symmetry; apply factors_compose.
- apply left_factor_L.
Qed.

End stuff.

Section stuff_2.
Context `(Category C).
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.
Context `(!WFS_factorization L R).
Context `(!WFS_lift (L:=L) (R:=R)).
Context `(!WFS_retract (P:=L)).
Context `(!WFS_retract (P:=R)).

Lemma wfs_R_retract_closed : forall `(F:u⟶v), WFS_lift (L:=L) (R:=(fun x y f => JMrelation.R equiv F _ equiv f)) → R F.
Proof.
intros.
apply (wfs_L_retract_closed (L:=dualP R) (R:=dualP L) ); try apply _.
apply (Dual_WFS_lift (WFS_lift0:=X)).
Qed.

End stuff_2.
