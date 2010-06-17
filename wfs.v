Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require JMrelation.
Require Import abstract_algebra functors categories.
Require dual.

(* me *)
Require Import square retract.

Set Implicit Arguments.
Section stuff.

Section ArrowClass.
Context `{Category C}.

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

Section moreArrowClass.
Context `{Category C}.
Context `{!ArrowClass P}.
Definition dualP := fun x y (f:dual.flipA x y) => P f.
Global Instance DualArrowClass: ArrowClass dualP.
Proof. repeat (try apply ArrowClass0; intro). Qed.
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

Class WFS_factorization := wfs_factorization :> forall `(f:x⟶y), Factorization f.

End Factorization.
Implicit Arguments factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments left_factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Implicit Arguments right_factor [[C][Arrows0][H][CatComp0][x][y][Factorization]].
Section moreFactorization.
Context `{Category C}.
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.

Global Instance Dual_factorization `(Q:WFS_factoriztion): WFS_factorization (L:=dualP R) (R:=dualP L).
Proof. intros x y f. do 3 red in f. 
Set Printing All. Show.
destruct H in Qf.
apply (factorization (L:=dualP R) (R:=dualP L) x y f (factor L R f) (right_factor L R f) (left_factor L R f)).
- apply right_factor_R0.
- apply left_factor_L0.
- apply factors_compose0.
Qed.

End moreFactorization.

Section Lift.

Class Lifting (a b x y:C) `(i:a⟶b) `(p:x⟶y) `(!Square i p (f:a⟶x) (g:b⟶y)) := lifting {
  lift: b⟶x;
  lift_left_commute: f = lift ◎ i;
  lift_right_commute: g = p ◎ lift
}.

Implicit Arguments Lifting [[a][b][x][y][Square0]].

Context `(ArrowClass L) `(ArrowClass R).
Class WFS_lift := wfs_lift :> forall (a b x y: C) (i:a⟶b) (p:x⟶y)  `(!Square i p f g) (_:L i) (_:R p), Lifting i p f g.

Global Instance: WFS_lift (L:=dualR) (R:=dualL).
Proof.
repeat intro.
do 3 red in i, p, f, g.
assert (Sq:Square p i g f).
  red; rewrite Square0; reflexivity.
pose (WFS_lift0 Sq H2 H1).
destruct l.
eapply lifting; do 2 red.
instantiate (1:=lift0).
- rewrite <- lift_right_commute0.
  reflexivity.
- rewrite <- lift_left_commute0.
  reflexivity.
Qed.
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

Lemma wfs_L_retract_closed : forall `(i:a⟶b), WFS_lift (fun x y f => JMrelation.R equiv i _ equiv f) R → L i.
Proof.
intros a b i lift_fR.
pose (r := right_factor L R i).
pose (l := left_factor L R i).
assert (Sq: Square i r l cat_id).
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

End stuff.

End stuff.

Section stuff_2.
Context `(Category C).
Context `{!ArrowClass L}.
Context `{!ArrowClass R}.
Context `(!WFS_factorization (L:=L)(R:=R)).
Context `(!WFS_lift (L:=L) (R:=R)).
Context `(!WFS_retract (L:=L)).
Context `(!WFS_retract (L:=R)).

Require dual.
Let dualL := fun x y (f:dual.flipA x y) => L f.
Let dualR := fun x y (f:dual.flipA x y) => R f.
Instance: ArrowClass dualL.
Proof. repeat (try apply ArrowClass0; intro). Qed.
Instance: ArrowClass dualR.
Proof. repeat (try apply ArrowClass1; intro). Qed.

Instance: WFS_factorization (L:=dualR) (R:=dualL).
Proof. intros x y f. do 3 red in f. destruct (WFS_factorization0 f).
apply (factorization (L:=dualR) (R:=dualL) x y f factor0 right_factor0 left_factor0).
- apply right_factor_R0.
- apply left_factor_L0.
- apply factors_compose0.
Qed.

Instance: WFS_lift (L:=dualR) (R:=dualL).
Proof.
repeat intro.
do 3 red in i, p, f, g.
assert (Sq:Square p i g f).
  red; rewrite Square0; reflexivity.
pose (WFS_lift0 Sq H2 H1).
destruct l.
eapply lifting; do 2 red.
instantiate (1:=lift0).
- rewrite <- lift_right_commute0.
  reflexivity.
- rewrite <- lift_left_commute0.
  reflexivity.
Qed.

Instance: WFS_retract (L:=dualR).
Proof.
repeat intro.
red. do 3 red in f, g, i, p, i', p'.
assert (Retract p' i' p i f g).
- destruct Retract0.
  split.
  + apply bottom.
  + apply top.
  + red. symmetry. apply sq_r.
  + red. symmetry. apply sq_l.
- red in H1.
apply (WFS_retract1 H2).
exact H1.
Qed.

Lemma wfs_R_retract_closed : forall `(F:a⟶b), WFS_lift (L:=L) (R:=(fun x y f => JMrelation.R equiv F _ equiv f)) → R F.
Proof.
intros.
apply (wfs_L_retract_closed (L:=dualR) (R:=dualL) ); try apply _.
repeat intro.
do 3 red in i, p, f, g.
assert (Square p i g f).
  red; rewrite Square0; reflexivity.
eapply lifting.
instantiate (1:=lift0).
- rewrite <- lift_left_commute.

rewrite 
do 3 red in f. 
eapply factorization.
pose (z := (factor (L:=L)(R:=R)(CatComp0:=CatComp0)(H:=H) (f:=f))).
Check factorization (factor (f:=f)) (right_factor (f:=f): dual.flipA factor a ) (left_factor (f:=f)).


