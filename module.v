Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra setoid.
Require Import rings.

(* me *)

Require Import extra_tactics.

Set Implicit Arguments.

Infix "<*>" := ralgebra_action (at level 30).

Class Rmodule `(ez: Equiv Scalar) `(ee: Equiv Elem) `{op: RalgebraAction Scalar Elem}
    szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
    elem_plus elem_zero elem_opp: Prop :=
  { rmodule_ring: @Ring Scalar ez szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
  ; rmodule_abgroup:> @AbGroup _ _ elem_plus elem_zero elem_opp
  ; rmodule_unital: `(1 <*> x = x)
  ; rmodule_action_proper:> Proper (ez ==> ee ==> ee) op
  ; rmodule_distr_l: `(x <*> (a & b) = (x <*> a) & (x <*> b))
  ; rmodule_distr_r: `((x + y) <*> a = (x <*> a) & (y <*> a))
  ; rmodule_assoc: `((x * y) <*> a = x <*> (y <*> a)) }.

Class Ralgebra `(ez: Equiv Scalar) `(e': Equiv Elem) `{RalgebraAction Scalar Elem}
    szalar_plus szalar_mult szalar_inv szalar_zero szalar_one
    elem_plus elem_mult elem_zero elem_one elem_opp: Prop :=
  { ralgebra_module:> Rmodule ez e'
      szalar_plus szalar_mult szalar_inv szalar_zero szalar_one
      elem_plus elem_zero elem_opp
  ; ralgebra_ring:> @Ring Elem e' elem_plus elem_mult elem_zero elem_one elem_opp
  ; ralgebra_assoc: `(x <*> (a * b) = (x <*> a) * b) }.

Section Morphisms.
Context `{Ring R} `{Rmodule R M} {r: R}.
Global Instance: Setoid_Morphism (ralgebra_action r).
Global Instance: SemiGroup_Morphism (ralgebra_action r).
Proof.
  intuition; constructor; try typeclasses eauto.
  apply rmodule_distr_l.
Qed.
Global Instance: Monoid_Morphism (ralgebra_action r).
Proof.
  intuition constructor; try typeclasses eauto.
  apply (right_cancel (r<*>-mon_unit)).
  rewrite left_identity.
  rewrite <- rmodule_distr_l.
  rewrite left_identity.
  apply rmodule_action_proper; try reflexivity.
Qed.

Global Instance SemiGroup_Morphism_id M `{SemiGroup M}: SemiGroup_Morphism (id: M→M).
Proof.
  constructor; try typeclasses eauto.
  unfold id; intuition.
Qed.
Global Instance Monoid_Morphism_id M `{Monoid M} : Monoid_Morphism (id: M→M).
Proof. constructor; try typeclasses eauto; reflexivity. Qed.

Require Import Program.
Require Import setoids.
Global Instance SemiGroup_Morphism_comp
    S T U `{SemiGroup S} `{SemiGroup T} `{SemiGroup U} (f: T→U) (g: S→T)
    `{!SemiGroup_Morphism f} `{!SemiGroup_Morphism g}
  : SemiGroup_Morphism (f∘g).
Proof.
  constructor; try typeclasses eauto.
  unfold compose. do 2 setoid_rewrite preserves_sg_op; reflexivity.
Qed.
Global Instance Monoid_Morphism_comp
    S T U `{Monoid S} `{Monoid T} `{Monoid U} (f: T→U) (g: S→T)
    `{!Monoid_Morphism f} `{!Monoid_Morphism g}
  : Monoid_Morphism (f∘g).
Proof.
  constructor; try typeclasses eauto.
  unfold compose; do 2 rewrite preserves_mon_unit; reflexivity.
Qed.

End Morphisms.

Require Import theory.rings.
Section Basic_Lemmas.
Context `{Ring R} `{Rmodule R M}.
Lemma rmodule_zero_action r: (0 <*> r = mon_unit).
Proof.
  apply (left_cancel (1<*>r)).
  rewrite <- rmodule_distr_r.
  rewrite (right_identity (1<*>r)).
  apply rmodule_action_proper; try reflexivity.
  apply right_identity.
Qed.
Lemma rmodule_minus: `((-r) <*> m = -r <*> m).
Proof.
  intros r m.
  apply inv_unique; left.
  rewrite <- (rmodule_distr_r).
  rewrite plus_opp_r.
  apply rmodule_zero_action.
Qed.
End Basic_Lemmas.


Section Rmodules.

Class Rmodule_Morphism Scalar M1 M2 {ez: Equiv Scalar} {e1: Equiv M1} `{RalgebraAction Scalar M1} {e2: Equiv M2} `{RalgebraAction Scalar M2}
    {szalar_plus} {szalar_mult} {szalar_zero: RingZero Scalar} {szalar_one: RingOne Scalar} {szalar_inv: GroupInv Scalar}
    {M1_plus} {M1_zero} {M1_opp} {M2_plus} {M2_zero} {M2_opp} (f: M1 -> M2) :=
{ rmodule_morphism_ring : @Ring Scalar ez szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
; rmodule_morphism_M1_abgroup: @Rmodule Scalar _ M1 _ _ _ _ _ _ _ M1_plus M1_zero M1_opp
; rmodule_morphism_M2_abgroup: @Rmodule  Scalar _ M2 _ _ _ _ _ _ _ M2_plus M2_zero M2_opp
; rmodule_morphism_groupmor:> Monoid_Morphism f
; preserves_rmodule_action: `(f (x <*> a) = x <*> f a)
}.

Global Instance Rmodule_Morphism_id `{Ring R} `{Rmodule R M}: Rmodule_Morphism (id: M→M).
Proof.
  constructor; try typeclasses eauto.
  reflexivity.
Qed.
Local Implicit Arguments Rmodule [[ez] [ee] [op]].

Global Instance Rmodule_Morphism_comp (R S T U: Type) `{Ring R}
  `{Rmodule R S, Rmodule R T, Rmodule R U}
  {f: T->U} (g: S->T)
  `{!Rmodule_Morphism f} `{!Rmodule_Morphism g}
  : Rmodule_Morphism (compose f g).
Proof.
  constructor; try typeclasses eauto.
  intros x a.
  unfold compose.
  do 2 rewrite preserves_rmodule_action; reflexivity.
Qed.

Context `{Ring R}.
Local Implicit Arguments Rmodule [[ez] [ee] [op] [szalar_plus] [szalar_mult] [szalar_inv] [szalar_zero] [szalar_one]].

Record Object :=
  { module :> Type
  ; mod_op:> RalgebraAction R module; eM: Equiv module; elem_plus: _ ; elem_zero: _; elem_opp: _
  ; rmodule:> Rmodule R module elem_plus elem_zero elem_opp
  }.
Global Existing Instance mod_op.
Global Existing Instance rmodule.
Global Existing Instance eM.
Global Existing Instance elem_plus.
Global Existing Instance elem_zero.
Global Existing Instance elem_opp.

Record Arrow (M N: Object) : Type := arrow
{ f:> M→N
; arrow_rmodmor:> Rmodule_Morphism f
}.
Implicit Arguments arrow [M N [f]].
Global Existing Instance arrow_rmodmor.

Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.
Section e. Context {M N: Object}.
Global Instance ea: Equiv (M ⟶ N) := fun f g => ∀ (m: M), f m = g m.
Instance: Equivalence ea.
Proof. prove_equivalence. Qed.

Global Instance: Setoid (M ⟶ N).
End e.

Global Instance xx `(e1: Equiv A): Proper (e1 ==> e1) `(id: A→A) := fun _ _ => id.

Global Instance:  CatId Object := fun x => arrow (f:= id) _.

Global Instance: CatComp Object := fun x y z f g =>  arrow (f:= compose f g) _.

Global Instance: ∀ x y z: Object,
    Proper (equiv ==> equiv ==> equiv) ((◎): (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
Proof.
  intros. intros a b Hab c d Hcd.
  unfold equiv, ea.
  simpl.
  unfold compose. unfold equiv, ea in Hab, Hcd.
  setoid_rewrite  Hab.
  setoid_rewrite Hcd.
  reflexivity.
Qed.

Let id_l' (x y: Object) (f: x⟶y): cat_id ◎ f = f.
Proof. intro; reflexivity. Qed.
Let id_r' (x y: Object) (f: x⟶y): f ◎ cat_id = f.
Proof. intro; reflexivity. Qed.

Lemma comp_assoc' (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z): c ◎ (b ◎ a) = (c ◎ b) ◎ a.
Proof. intro; reflexivity. Qed.

Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.

Section Kernel.
Context {M N: Type}.

(* TODO: This should be in terms of pointed setoids. *)
Context `{Monoid M, Monoid N} (f: M→N) `{!Monoid_Morphism f}.
Definition Kernel := {m: M | f m = mon_unit}.
Global Instance e: Equiv Kernel := fun k k' => `k = `k'.
Instance: Equivalence e.
Global Instance: Setoid Kernel.
Global Program Instance Kop: SemiGroupOp Kernel := fun k k' => exist _ (`k & `k') _.
Next Obligation.
  rewrite preserves_sg_op.
  destruct k as [k Hk], k' as [k' Hk']; simpl.
  rewrite Hk, Hk'.
  apply left_identity.
Qed.
Global Instance: Proper (e==>e==>e) sg_op.
Proof.
  intros [??][??]?[??][??]?.
  unfold e; simpl.
  apply sg_mor; assumption.
Qed.
Global Instance: Associative Kop.
Proof.
  intros [??][??][??].
  unfold equiv, e, Kop; simpl.
  apply (sg_ass _).
Qed.
Global Instance: SemiGroup Kernel.
Global Program Instance: MonoidUnit Kernel := exist _ mon_unit preserves_mon_unit.
Global Instance: LeftIdentity Kop mon_unit.
Proof. intros [??]; unfold equiv, e, mon_unit, MonoidUnit_instance_0; simpl; apply left_identity. Qed.
Global Instance: RightIdentity Kop mon_unit.
Proof. intros [??]; unfold equiv, e, mon_unit, MonoidUnit_instance_0; simpl; apply right_identity. Qed.
Global Instance: Monoid Kernel.
Let  i: Kernel→M := @projT1 _ _.
Global Instance: Proper (e==>equiv) i.
Proof. intros [??][??]?; unfold i; simpl; assumption. Qed.
Global Instance x(*TODO: Name?*): Setoid_Morphism (@projT1 _ _:Kernel->M).
Global Instance: SemiGroup_Morphism (@projT1 _ _:Kernel->M).
Proof.
  constructor; try typeclasses eauto.
  intros [??][??]; reflexivity.
Qed.
Global Instance Monoid_instance_1: Monoid_Morphism (@projT1 _ _:Kernel->M).
Proof.
 constructor; try typeclasses eauto; reflexivity.
Qed.
Context `{!Commutative sg_op}.
Global Instance: Commutative (A:=Kernel) sg_op.
Proof. intros [??][??]; unfold equiv, e; simpl; apply commutativity. Qed.
End Kernel.

Section Kernel_Group.
(* TODO: This only needs that M is a monoid. *)
Context `{Group M, Group N} (f: M→N) `{!Monoid_Morphism f}.
Global Program Instance: GroupInv (Kernel f) := fun k => exist _ (-`k) _.
Next Obligation.
  destruct k as [k Hk]; simpl.
  rewrite preserves_inv, Hk; try typeclasses eauto.
  exact inv_zero.
Qed.
Global Instance: Proper (equiv==>equiv) (group_inv (A:=Kernel f)).
Proof. intros [??][??]?; unfold equiv, e; simpl; apply inv_proper; assumption. Qed.
(* TODO: Define LeftInverse and RightInverse classes. *)
Global Instance Kernel_Group: Group `{Kernel f}.
Proof.
  constructor; try typeclasses eauto
  ; intros [??]; unfold equiv, e; simpl; [apply ginv_l | apply ginv_r].
Qed.
End Kernel_Group.
Section Kernel_AbGroup.
Context `{AbGroup M, AbGroup N} (f: M→N) `{!Monoid_Morphism f}.
(* TODO: This only needs a sub semigroup to prove. *)
Global Instance: AbGroup (Kernel f).
End Kernel_AbGroup.

Section Kernel_Rmodule.
Context `{Ring R} `{Rmodule R M, Rmodule R N} (f: M→N) `{!Rmodule_Morphism f}.
Global Program Instance rk: RalgebraAction R (Kernel f) := fun r k => exist _ (r<*>` k) _.
Next Obligation.
  destruct k as [k Hk]; simpl.
  rewrite preserves_rmodule_action, Hk.
  apply preserves_mon_unit.
Qed.
Global Instance: !Rmodule R (Kernel f).
Proof.
  constructor; try typeclasses eauto; unfold equiv, e, Proper, "==>"; intuition;
    repeat match goal with
      | [ x : Kernel f |- _ ] => destruct x
    end; simpl.
  * apply rmodule_unital.
  * apply rmodule_action_proper; assumption.
  * apply rmodule_distr_l.
  * apply rmodule_distr_r.
  * apply rmodule_assoc.
Qed.

Global Instance: Rmodule_Morphism (@projT1 _ _:Kernel f→M).
Proof.
  constructor; try typeclasses eauto.
  intros ?[??]; simpl; reflexivity.
Qed.

End Kernel_Rmodule.


Context `{M: nat → Type}.
Context `{forall n: nat, Rmodule R (e:=e) (M n)}.
