Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra setoid.

(* me *)

Require Import extra_tactics.

Set Implicit Arguments.

Infix "<*>" := ralgebra_action (at level 30).

Class Rmodule `(ez: Equiv Scalar) `(ee: Equiv Elem) `{op: RalgebraAction Scalar Elem}
    szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
    elem_plus elem_zero elem_opp: Prop :=
  { rmodule_ring: @Ring Scalar ez szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
  ; rmodule_abgroup:> @AbGroup _ _ elem_plus elem_zero elem_opp
  ; rmodule_action: `(1 <*> x = x)
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

Require Import theory.rings.
Section Basic_Lemmas.
Context `{Ring R} `{Rmodule R M}.
Goal `((-(1)) <*> m = - m).
  intro m.
  apply inv_unique; left.
  setoid_rewrite <- (rmodule_action m) at 1.
  rewrite <- (rmodule_distr_r).
  rewrite plus_opp_r.
Goal `(0 <*> r = mon_unit).
Proof.
  intro m.
  rewrite <- (left_absorb 0).

Goal `(r <*> mon_unit = mon_unit).


  Typeclasses eauto := .
Section Rmodules.


Class Rmodule_Morphism Scalar M1 M2 {ez: Equiv Scalar} {e1: Equiv M1} `{RalgebraAction Scalar M1} {e2: Equiv M2} `{RalgebraAction Scalar M2}
    {szalar_plus} {szalar_mult} {szalar_zero: RingZero Scalar} {szalar_one: RingOne Scalar} {szalar_inv: GroupInv Scalar}
    {M1_plus} {M1_zero} {M1_opp} {M2_plus} {M2_zero} {M2_opp} (f: M1 -> M2) :=
{ rmodule_morphism_ring : @Ring Scalar ez szalar_plus szalar_mult szalar_zero szalar_one szalar_inv
; rmodule_morphism_M1_abgroup: @Rmodule Scalar _ M1 _ _ _ _ _ _ _ M1_plus M1_zero M1_opp
; rmodule_morphism_M2_abgroup: @Rmodule  Scalar _ M2 _ _ _ _ _ _ _ M2_plus M2_zero M2_opp
; rmodule_morphism_groupmor:> Group_Morphism f
; preserves_rmodule_action: `(f (x <*> a) = x <*> f a)
}.

Global Instance Rmodule_Morphism_id `{Ring R} `{Rmodule R M}: Rmodule_Morphism (id: M→M).
Proof.
  constructor; try typeclasses eauto. 
  reflexivity.
Qed.
Local Implicit Arguments Rmodule [[ez] [ee] [op]].

Global Instance Rmodule_Morphism_comp (R S T U: Type) `{Ring R}
  `{Rmodule R S }
 `{ Rmodule R T, Rmodule R U} 

 {f: T->U} (g: S->T)
  `{!Rmodule_Morphism f} `{!Rmodule_Morphism g}
 : Rmodule_Morphism (compose f g).
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
Typeclasses eauto := debug 10.
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
unfold compose. unfold equiv, ea in Hab, Hcd. setoid_rewrite  Hab.
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

Context M N `{Rmodule R M} `{Rmodule R N} (f:M->N) `{!Rmodule_Morphism f}.
Definition K : Type := {m: M | f m = mon_unit}.
Instance: Equiv K := fun k k' => `k = `k'.
Context (r:R) (k:K).
Goal f (r <*> `k) = mon_unit.
rewrite preserves_rmodule_action.
destruct k; simpl. 
rewrite e.
Goal r <*> mon_unit = mon_unit.
rewrite <- (ginv_l mon_unit) at 1. 
rewrite rmodule_distr_l.
apply 
rewrite (proj2_sig k).
Program Instance: RalgebraAction R K := fun r k => r <*> ` k.
Obligation 2.
apply True.
Defined.
Obligation 3.
destruct k; assumption.
Qed.
Obligation 4.
unfold RalgebraAction_instance_0_obligation_2. auto.
Defined.
Obligation 1.
red.
intros.
refine (X <*> `X0).

Typeclasses eauto :=. 

Next Obligation.
 

Context `{M: nat → Type}.
Context `{forall n: nat, Rmodule R (e:=e) (M n)}.

