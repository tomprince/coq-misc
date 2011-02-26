Require Import
   Morphisms RelationClasses Equivalence Setoid Program
   abstract_algebra varieties.setoid semigroup.
Require Import rings groups.

(* me *)

Require Import extra_tactics.

(*Set Implicit Arguments.*)

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

Ungereralizable Arguments  Rmodule [ez szalar_plus szalar_mult szalar_zero szalar_one szalar_inv].

Class Ralgebra `(ez: Equiv Scalar) `(e': Equiv Elem) `{RalgebraAction Scalar Elem}
    szalar_plus szalar_mult szalar_inv szalar_zero szalar_one
    elem_plus elem_mult elem_zero elem_one elem_opp: Prop :=
  { ralgebra_module:> Rmodule ez e'
      szalar_plus szalar_mult szalar_inv szalar_zero szalar_one
      elem_plus elem_zero elem_opp
  ; ralgebra_ring: @Ring Elem e' elem_plus elem_mult elem_zero elem_one elem_opp
  ; ralgebra_assoc: `(x <*> (a * b) = (x <*> a) * b) }.

Implicit Arguments left_cancellation [[A][e][op][LeftCancellation]].
Implicit Arguments right_cancellation [[A][e][op][RightCancellation]].
(*
Global Instance SemiGroup_Morphism_id M `{SemiGroup M}: SemiGroup_Morphism (id: M→M).
Proof.
  constructor; try typeclasses eauto.
  unfold id; intuition.
Qed.
Global Instance Monoid_Morphism_id M `{Monoid M} : Monoid_Morphism (id: M→M).
Proof. constructor; try typeclasses eauto; reflexivity. Qed.
*)

Section Morphisms.
Context `{Ring R} `{Rmodule R M} {r: R}.
Global Instance: SemiGroup_Morphism (ralgebra_action r).
Proof.
  intuition constructor; try typeclasses eauto.
  constructor; try typeclasses eauto.
  apply rmodule_distr_l.
Qed.
Global Instance: Monoid_Morphism (ralgebra_action r).
Proof.
  intuition constructor; try typeclasses eauto.
  apply (right_cancellation (r<*>-mon_unit)).
  rewrite left_identity.
  rewrite <- rmodule_distr_l.
  rewrite left_identity.
  apply rmodule_action_proper; try reflexivity.
Qed.

End Morphisms.

Require Import theory.rings.
Section Basic_Lemmas.
Context `{Ring R} `{Rmodule R M}.
Lemma rmodule_zero_action r: (0 <*> r = mon_unit).
Proof.
  apply (left_cancellation (1<*>r)).
  rewrite <- rmodule_distr_r.
  rewrite (right_identity (1<*>r)).
  apply rmodule_action_proper; try reflexivity.
  apply right_identity.
Qed.
Lemma rmodule_minus: `((-r) <*> m = -r <*> m).
Proof.
  intros r m.
  apply (left_cancellation (r<*>m)).
  rewrite <- (rmodule_distr_r).
  do 2 rewrite right_inverse.
  apply rmodule_zero_action.
Qed.
End Basic_Lemmas.


Section Rmodules.

Class Rmodule_Morphism {Scalar M1 M2: Type} {ez: Equiv Scalar} {e1: Equiv M1} `{RalgebraAction Scalar M1} {e2: Equiv M2} `{RalgebraAction Scalar M2}
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

End Rmodules.

Section Kernel.
Context {M N: Type}.

(* TODO: This should be in terms of pointed setoids. *)
Context `{Monoid M, Monoid N} (f: M→N) `{!Monoid_Morphism f}.
Definition Kernel := {m: M | f m = mon_unit}.
Global Instance ee: Equiv Kernel := fun k k' => `k = `k'.
Instance: Equivalence ee.
Global Instance: Setoid Kernel.
Global Program Instance Kop: SemiGroupOp Kernel := fun k k' => exist _ (`k & `k') _.
Next Obligation.
  rewrite preserves_sg_op.
  destruct k as [k Hk], k' as [k' Hk']; simpl.
  rewrite Hk, Hk'.
  apply left_identity.
Qed.
Global Instance: Proper (ee==>ee==>ee) sg_op.
Proof.
  intros [??][??]?[??][??]?.
  unfold ee; simpl.
  apply sg_mor; assumption.
Qed.
Global Instance: Associative Kop.
Proof.
  intros [??][??][??].
  unfold equiv, ee, Kop; simpl.
  apply (sg_ass _).
Qed.
Global Instance: SemiGroup Kernel.
Global Program Instance: MonoidUnit Kernel := exist _ mon_unit preserves_mon_unit.
Global Instance: LeftIdentity Kop mon_unit.
Proof. intros [??]; unfold equiv, ee, mon_unit, MonoidUnit_instance_0; simpl; apply left_identity. Qed.
Global Instance: RightIdentity Kop mon_unit.
Proof. intros [??]; unfold equiv, ee, mon_unit, MonoidUnit_instance_0; simpl; apply right_identity. Qed.
Global Instance: Monoid Kernel.
Let  i: Kernel→M := @projT1 _ _.
Global Instance: Proper (equiv==>equiv) i.
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
Proof. intros [??][??]; unfold equiv, ee. simpl; apply commutativity. Qed.
End Kernel.

Section Kernel_Group.
(* TODO: This only needs that M is a monoid. *)
Context `{Group M, Group N} (f: M→N) `{!Monoid_Morphism f}.
Global Program Instance: GroupInv (Kernel f) := fun k => exist _ (-`k) _.
Next Obligation.
  destruct k as [k Hk]; simpl.
  rewrite preserves_inv, Hk; try typeclasses eauto.
  exact inv_0.
Qed.
Global Instance: Proper (equiv==>equiv) (group_inv (A:=Kernel f)).
Proof. intros [??][??]?; unfold equiv, ee; simpl; apply inv_proper; assumption. Qed.
(* TODO: Define LeftInverse and RightInverse classes. *)
Global Instance Kernel_Group: Group `{Kernel f}.
Proof.
  constructor; try typeclasses eauto
  ; intros [??]; unfold equiv, ee; simpl; [apply ginv_l | apply ginv_r].
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
  constructor; try typeclasses eauto; unfold equiv, ee, Proper, "==>"; intuition;
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

Inductive Cokernel `(f:M→N)  := cok { sec : N }.
Implicit Arguments cok [[M] [N] [f]].
Implicit Arguments sec [[M] [N] [f]].
Section CoKernel.
Context {M N: Type}.

(* TODO: Define this more generally *)
Context `{AbGroup M, AbGroup N} (f: M→N) `{!Monoid_Morphism f}.
Local Notation Cokernel := (Cokernel f).
Global Instance eck: Equiv Cokernel := fun x y => ∃ k: M, sec x = f(k) & sec y.
Global Instance: Equivalence eck.
Proof. constructor.
  * intro x; exists mon_unit.
    rewrite preserves_mon_unit, left_identity; reflexivity.
  * intros x y [k Hk]; exists (-k).
    rewrite preserves_inv; try typeclasses eauto.
    apply (left_cancellation (f k)).
    rewrite <- Hk, sg_ass, ginv_r, left_identity; try typeclasses eauto.
    reflexivity.
  * intros x y z [k Hk] [k' Hk'].
    exists (k & k').
    rewrite preserves_sg_op, Hk, Hk', sg_ass; try typeclasses eauto.
    reflexivity.
Qed.
Global Instance: Setoid Cokernel.
Global Instance: Proper (equiv ==> equiv) cok.
Proof.
  intros ???. exists mon_unit. simpl.
  rewrite preserves_mon_unit, left_identity; assumption.
Qed.
Global Instance Setoid_Morphism_instance_1: Setoid_Morphism (cok:N→Cokernel).
Global Instance: SemiGroupOp Cokernel := fun x y => cok (sec x & sec y).
Global Instance: Associative (A:=Cokernel) sg_op.
Proof.
  intros x y z. 
  exists mon_unit.
  rewrite preserves_mon_unit, left_identity.
  destruct x, y, z. simpl.
  apply sg_ass.
  typeclasses eauto.
Qed.
Global Instance: Proper (equiv==>equiv==>equiv) (sg_op:_->_->Cokernel).
Proof.
  intros [?][?][k Hk] [?][?][k' Hk']. 
  exists (k & k'); simpl.
  setoid_rewrite Hk.  setoid_rewrite Hk'.
  rewrite <- sg_ass at 1 by typeclasses eauto.
  setoid_rewrite sg_ass at 2; try typeclasses eauto.
  setoid_rewrite commutativity at 3. simpl.
  repeat rewrite sg_ass by typeclasses eauto.
  rewrite <- preserves_sg_op, <- sg_ass.
  reflexivity.
  typeclasses eauto.
Qed.
Global Instance: Commutative (A:=Cokernel) sg_op.
Proof.
  intros x y.
  destruct x, y.
  exists mon_unit; rewrite preserves_mon_unit, left_identity.
  simpl; apply commutativity.
Qed.
Global Instance: SemiGroup Cokernel.
Global Instance: SemiGroup_Morphism cok.
Proof. constructor; try typeclasses eauto; reflexivity. Qed.
Global Instance: MonoidUnit Cokernel := cok mon_unit.
Global Instance: LeftIdentity sg_op (mon_unit:Cokernel).
Proof.
  intros [x].
  exists mon_unit; rewrite preserves_mon_unit. 
  simpl; reflexivity.
Qed.
Global Instance: RightIdentity sg_op (mon_unit:Cokernel).
Proof.
  intros [x].
  exists mon_unit; rewrite preserves_mon_unit.
  simpl.
  rewrite left_identity.
  apply right_identity.
Qed.
Global Instance: Monoid Cokernel.
Global Instance Monoid_Morphism_1: Monoid_Morphism cok.
Proof. constructor; try typeclasses eauto; reflexivity. Qed.
Global Instance: GroupInv Cokernel := fun x => cok (- sec x).
Global Instance: Proper (equiv ==> equiv) (group_inv:_->Cokernel).
Proof.
  intros [?][?][k Hk]; exists (-k). simpl.
  rewrite Hk, sg_inv_distr, (preserves_inv k).
  reflexivity.
Qed.
Global Instance: Group Cokernel.
Proof.
  constructor; try typeclasses eauto.
  * intros [x]. exists mon_unit. rewrite preserves_mon_unit, right_identity. simpl. apply ginv_l.
  * intros [x]. exists mon_unit. rewrite preserves_mon_unit, right_identity. simpl. apply ginv_r.
Qed.
Global Instance: AbGroup Cokernel.
End CoKernel.
Section Cokernel_Rmodule.
Context {M N: Type}.
Context `{Ring R} `{Rmodule R M, Rmodule R N} (f: M→N) `{!Rmodule_Morphism f}.
(*cpdt*)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ => idtac
  end.
Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.
(*Local Hint Extern 0 AbGroup => match goal with 
  [ x : Rmodule _ _ _ _ _ _ _ _ _ _ |- _ ] => extend (rmodule_abgroup (Rmodule:=x))
end : typeclass_instances.*)
(*TODO: pereformance hack *)
Let ABM := (rmodule_abgroup (Rmodule:=H0)).
Let ABN := (rmodule_abgroup (Rmodule:=H1)).
Existing Instance ABM.
Existing Instance ABN.
(* end preformance hack *)
Global Instance: RalgebraAction R (Cokernel f) := fun r n => cok (r <*> sec n).
Global Instance: Proper (equiv ==> eck f ==> eck f) ralgebra_action.
Proof.
  intros ? r Hr [?][?][k Hk]. exists (r <*> k).
  simpl.
  rewrite Hk, preserves_rmodule_action; simpl.
  rewrite <- rmodule_distr_l.
  apply rmodule_action_proper; [assumption | reflexivity].
Qed.
Global Instance: !Rmodule R (ee:=eck f) (Cokernel f).
Proof.
  constructor; try typeclasses eauto.
  Ltac simpl_cok := exists mon_unit; rewrite preserves_mon_unit, left_identity; simpl.
  * intros [x]; simpl_cok. apply rmodule_unital.
  * intros r [a] [b]; simpl_cok; apply rmodule_distr_l.
  * intros r s [a]; simpl_cok; apply rmodule_distr_r.
  * intros r s [a]; simpl_cok; apply rmodule_assoc.
Qed.
Global Instance Rmodule_Morphism_1: Rmodule_Morphism (e2:=eck f) cok.
Proof. constructor; try typeclasses eauto; reflexivity. Qed.
End Cokernel_Rmodule.

Section Exact.
Context {M N O: Type} `{Monoid M, Monoid N, Monoid O}.
Context (f: M→N) (g: N→O) `{!Monoid_Morphism f, !Monoid_Morphism g}.

Class Exact: Type := (* FIXME: Type *)
{ image_in_kernel : ∀ m, g (f m) = mon_unit
; kernel_in_image : ∀ n, g n = mon_unit → ∃ m , f m = n
}.
Class Mono: Prop := mono: ∀ m m', f m = f m' → m = m'.
Class Epi: Prop := epi: ∀ o, ∃ m, g m = o.
Class ShortExact :=
{ exact1 : Mono
; exact2 : Exact
; exact3 : Epi
}.

Lemma mono_preserves_unit `{Mono}: ∀ m, f m = mon_unit → m = mon_unit.
Proof.
  intros m Hm.
  apply mono.
  rewrite preserves_mon_unit; assumption.
Qed.
End Exact.
Section Exact2.
Context {M N O: Type} `{AbGroup M, AbGroup N, AbGroup O}.
Context (f: M→N) (g: N→O) `{!Monoid_Morphism f, !Monoid_Morphism g}.
Context `{!Exact f g}.
(* FIXME: naming *)
Lemma exact_equal_epi n n': g n = g n' ↔ ∃ m, n = f m & n'.
Proof.
  split.
  * intro Hn.
    assert (g (n & -(n')) = mon_unit).
    rewrite preserves_sg_op, Hn, <- preserves_sg_op.
    rewrite ginv_r.
    apply preserves_mon_unit.
    set (m := kernel_in_image f g (n & -n')).
    destruct m as [m Hm]; [assumption | exists m].
    rewrite Hm, <- sg_ass, ginv_l, right_identity; try typeclasses eauto.
    reflexivity.
  * intros [m Hm].
    rewrite Hm.
    rewrite preserves_sg_op.
    rewrite <- (left_identity (g n')) at 2.
    apply sg_mor; [| reflexivity ].
    apply (image_in_kernel f g m).
Qed.
End Exact2.

Tactic Notation "unfold_equiv" "in" hyp(H) :=
  match type of H with
    | context ctx [@equiv ?A ?eq ?a ?b ]  =>
      let T := eval red in (@equiv A eq a b) in
      let T := eval red in T in
        let new := context ctx[T] in change new in H; simpl in H
  end.
Local Ltac unfold_equiv :=
  match goal with
    | [ |- context ctx [@equiv ?A ?eq ?a ?b ]]  =>
      let T := eval red in (@equiv A eq a b) in
      let T := eval red in T in
        let new := context ctx[T] in change new; simpl
  end.

Section SnakePart1.
(** TODO: Use squares for this. (requires us to be working in a category **)
Context {M N M' N'} `{Monoid M, Monoid N, Monoid M', Monoid N'}.
Context (i: M→N) (i': M'→N') (f: M→M') (g: N→N').
(** TODO: Express square using ∘ **)
Context {Sq: ∀ m, g (i m) = i' (f m)}.
Context `{!Monoid_Morphism i, !Monoid_Morphism i', !Monoid_Morphism f, !Monoid_Morphism g}.

Program Definition KernelMap: Kernel f → Kernel g := fun m => i m.
Next Obligation.
  rewrite Sq.
  destruct m as [m Hm]; simpl.
  rewrite Hm. apply preserves_mon_unit.
Qed.

Global Instance: Proper (equiv ==> equiv) KernelMap.
Proof.
  intros [x Hx] [y Hy] Hxy.
  unfold_equiv.
  apply sm_proper; assumption.
Qed.
Global Instance Setoid_Morphism_instance_2: Setoid_Morphism KernelMap.
Global Instance: SemiGroup_Morphism KernelMap.
Proof.
  constructor; try typeclasses eauto.
  intros [m Hm] [n Hn].
  unfold_equiv.
  apply preserves_sg_op.
Qed.
Global Instance Monoid_Morphism_instance_1: Monoid_Morphism KernelMap.
Proof.
  constructor; try typeclasses eauto.
  unfold_equiv.
  apply preserves_mon_unit.
Qed.

Context `{!Mono i}.
Global Instance: Mono KernelMap.
  intros [??] ? Hm.
  unfold_equiv in Hm .
  apply (mono i); assumption.
Qed.
End SnakePart1.

Section SnakePart2.
(** FIXME: Copied from SnakePart1 **)
Context {M N M' N'} `{AbGroup M, AbGroup N, AbGroup M', AbGroup N'}.
Context (i: M→N) (i': M'→N') (f: M→M') (g: N→N').
Context {Sq: ∀ m, g (i m) = i' (f m)}.
Context `{!Monoid_Morphism i, !Monoid_Morphism i', !Monoid_Morphism f, !Monoid_Morphism g}.
Definition CokernelMap: Cokernel f → Cokernel g := fun x => cok (i' (sec x)).
Global Instance: Proper ((eck f) ==> (eck g)) CokernelMap.
Proof.
  intros [m] [n] [k Hk].
  exists (i k). simpl.
  rewrite Sq.
  rewrite <- preserves_sg_op.
  apply sm_proper; assumption.
Qed.
Global Instance Setoid_Morphism_instance_3: Setoid_Morphism (Aeq:=eck f) (Beq:=eck g) CokernelMap.
Global Instance: SemiGroup_Morphism (Aeq:=eck f) (Beq:=eck g) CokernelMap.
Proof.
  constructor; try typeclasses eauto.
  intros [m] [n]; exists (mon_unit:N); simpl.
  rewrite <- preserves_sg_op.
  rewrite preserves_mon_unit.
  symmetry; apply left_identity.
Qed.
Global Instance Monoid_Morphism_2: Monoid_Morphism (Aeq:=eck f) (Beq:= eck g) CokernelMap.
Proof.
  constructor; try typeclasses eauto.
  exists (mon_unit:N); simpl.
  do 2 rewrite preserves_mon_unit.
  symmetry; apply right_identity.
Qed.
End SnakePart2.

Section SnakePart3.
Context M N O M' N' O'  `{AbGroup M, AbGroup N, AbGroup O, AbGroup M', AbGroup N', AbGroup O'}.
Context (i: M→N) (p: N→O) (i': M'→N') (p': N'→O') (f: M→M') (g: N→N') (h: O→O').
Context {Sq_l: ∀ m, g (i m) = i' (f m)} {Sq_r: ∀ n, h (p n) = p' (g n)}.
Context `{!Monoid_Morphism i, !Monoid_Morphism p, !Monoid_Morphism i', !Monoid_Morphism p'}.
Context `{!Monoid_Morphism f, !Monoid_Morphism g, !Monoid_Morphism h}.

Context `{!Mono i'} `{!Exact i p}.
Global Instance: Exact (KernelMap i i' f g (Sq:=Sq_l)) (KernelMap p p' g h (Sq:=Sq_r)).
Proof.
  split.
  * intros [m Hm].
    unfold_equiv.
    apply image_in_kernel.
    assumption.
  * intros [n Hn] Hn'. 
    unfold_equiv in Hn'.
    set (m := kernel_in_image i p n).
    destruct m as [m Hm]; [assumption | ].
    assert (Hm': f m = mon_unit).
    - apply (mono_preserves_unit i').
      rewrite <- Sq_l.
      rewrite Hm; assumption.
    - eexists (exist (fun m => f m = mon_unit) m Hm').
      unfold_equiv; assumption.
Qed.

Context `{!Epi p} `{!Exact i' p'}.
Global Instance: Exact (e0:=eck g)(e1:=eck h) (CokernelMap i' f g) (CokernelMap p' g h).
Proof.
  split.
  * intros m.
    unfold CokernelMap in *.
    unfold_equiv.
    exists (p mon_unit:O).
    rewrite right_identity.
    rewrite Sq_r.
    erewrite (exact_equal_epi i' p').
    exists (sec m).
    rewrite preserves_mon_unit.
    symmetry; apply right_identity.
  * intros n Hn.
    unfold CokernelMap in *.
    unfold_equiv in Hn.
    destruct Hn as [o Ho].
    rewrite right_identity in Ho.
    destruct (epi p o) as [n' Hn'].
    rewrite <- Hn', Sq_r in Ho; clear o Hn'.
    destruct (kernel_in_image i' p' (- (g n') & sec n)) as [m Hm].
    rewrite preserves_sg_op, Ho, preserves_inv; try typeclasses eauto.
    apply left_inverse.
    exists (@cok _ _ f m).
    unfold_equiv.
    exists (- n').
    rewrite preserves_inv; try typeclasses eauto.
    assumption.
Qed.

Context {Choice: ∀ A B (f: A→B) `{Equiv B} (b: B), (∃ a:A, f a = b) → {a | f a = b}}.
Implicit Arguments Choice [[A][B][H5]].

Lemma fChoice {A B} (F: A→B) `{Equiv B} b a: F (` (Choice F b a)) = b.
Proof.
  set (a' := Choice F b a).
  destruct a' as [a' Ha'].
  apply Ha'.
Qed.

Program Definition Snake : Kernel h → Cokernel f := fun o => cok (Choice i' _ (kernel_in_image i' p' (g (Choice p o (epi p o))) _)).
Next Obligation.
  destruct o as [o Ho].
  rewrite <- Sq_r. 
  simpl. 
  rewrite fChoice.
  assumption.
Qed.

Global Instance: Exact (e1:=eck f)  (KernelMap p p' g h (Sq:=Sq_r)) Snake.
split.
* intros [n Hn].
  unfold_equiv. setoid_rewrite right_identity.
  unfold Snake, KernelMap; simpl.
  set (n' := Choice _ _ (epi p (p n))).
  assert ((p (-n &  ` n')) = mon_unit) by (destruct n' as [n' Hn']; rewrite preserves_sg_op, preserves_inv, Hn', left_inverse; try reflexivity; typeclasses eauto).
  destruct (kernel_in_image i p (-n & `n') H5) as [m Hm].
  exists m.
  apply (mono i').
  rewrite fChoice.
  rewrite <- Sq_l, Hm, preserves_sg_op, preserves_inv; try typeclasses eauto.
  rewrite Hn, inv_0, left_identity.
  reflexivity.
* intros [o Ho]. 
  unfold Snake.
  simpl.
  set (n:= Choice _ _ (epi p o)).
  intros [m Hm].  
  rewrite right_identity in Hm.
  assert (g (` n & - i m) = mon_unit) by (
    rewrite preserves_sg_op, preserves_inv; try typeclasses eauto;
    rewrite Sq_l, <- Hm; simpl; rewrite fChoice;
    apply right_inverse).
  exists (exist (fun n => g n = mon_unit) (`n & - i m) H5).
  unfold_equiv.
  rewrite preserves_sg_op, preserves_inv; try typeclasses eauto.
  subst n.
  rewrite fChoice.
  rewrite (image_in_kernel i p), inv_0.
  apply right_identity.
Qed.

Global Instance: Exact (e0:=eck f) (e1:=eck g)  Snake (fun x => cok (i' (sec x))).
Proof.
split.
* intros [o Ho]. 
  unfold Snake. simpl.
  rewrite fChoice.
  simpl; set (n:= Choice _ _ (epi p o)).
  unfold_equiv; exists (` n).
  symmetry; apply right_identity.
* intros m' Hm'.
  unfold_equiv in Hm'.
  setoid_rewrite right_identity in Hm'.
  assert (∃ k: N, g k = i' (sec m')) by (destruct Hm' as [n Hn]; exists n; symmetry; exact Hn).
  clear Hm'; apply Choice in H5; destruct H5 as [n Hn].
  assert (h (p n) = mon_unit) by (rewrite Sq_r, Hn; apply image_in_kernel; typeclasses eauto).
  exists (exist (fun o => h o = mon_unit) (p n) H5).
  unfold Snake.
  unfold_equiv.
  set (n' :=  (Choice p (p n) (epi p (p n)))).
  assert (p (`n' & -n) = mon_unit) by (destruct n' as [n' Hn']; rewrite preserves_sg_op, preserves_inv, Hn'; try apply right_inverse; typeclasses eauto).
  set (m := Choice i _ (kernel_in_image i p (`n'&-n) H6)).
  destruct m as [m Hm].
  exists m.
  apply (mono i').
  rewrite fChoice.
  rewrite preserves_sg_op, <- Sq_l.
  rewrite <- Hn, <- preserves_sg_op.
  rewrite Hm.
  rewrite <- sg_ass, left_inverse, right_identity; try typeclasses eauto.
  reflexivity.
Qed.
End SnakePart3.
