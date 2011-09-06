Set Automatic Coercions Import.
Require Import
   Morphisms RelationClasses Equivalence Setoid Arith
   abstract_algebra util canonical_names orders interfaces.orders.
Require setoids.
(* me *)

Require Import workaround_tactics.
Require Import interfaces.functors.
Require Import extra_tactics.
Require Import theory.categories.
Require categories.functors.

Require Import Program. 
Set Inconsistent Universes.
Require Import hom_functor.
Require Import peano_naturals.
Require Import theory.setoids.
Require Import orders.maps.
Require categories.orders.

Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.

Require Import theory.left_hereditary.
Require Import theory.powerset.
Require Import categories.induced.

Section Delta.

Inductive Object : Set := {D'' :> nat}.
Coercion Build_Object: nat >-> Object.
Definition D' (n:Object) :=  {x: nat | x ≤ n}.
Coercion D': Object >-> Sortclass.

Existing Instances po_setoid.

Require Import order.induced.

Instance Equiv_instance_1: Equiv (D' n) := fun n => sig_equiv _.
Definition D n := @orders.object (D' n) _ (induced.Le_instance_0 _ _ (@proj1_sig _ _ )) _ _.

 
Section ord.
  Context `{PartialOrder A} `{PartialOrder B} `{!OrderPreserving  (f: A→B)}.
  Global Instance HHH : Proper ((=) ==> (=)) f.
  Proof.
    intros a b Hab.
    apply (antisymmetry (≤));
      apply order_preserving; auto;
        eapply po_proper; try apply Hab; try reflexivity.
  Qed.
End ord.

Require categories.dual.
(* FIXME FIXME *)
Instance: Arrows Object := dual.flipA (A:=InducedArrow _ D).

Global Instance Equiv_instance_2: forall x y:Object, Equiv (x⟶y) := _.
Global Instance: CatComp Object := _.
Global Instance: CatId Object := _.
Global Instance: Category Object := dual.cat.

Notation sSet := (functors.Object Object setoids.Object).
Definition Δ (n: Object) := functors.object (homFrom n).

Definition misses {A} `{Equiv B} x (f: A->B) := forall y, ~ f y = x.

Section δΛΔ.
Let FF: ∀ n:Object, ∀ (c:n) (m:Object) (f: n ⟶ m), _ := λ C c x f, misses c (` f).
Instance: ∀ (n:Object) (c:n), LeftHereditary n (FF n c).
Proof.
  repeat intro.
  eapply H.
  apply_simplified H0.
Qed.

Let FFdD:  forall n:Object, ∀ (m:Object) (f: n ⟶ m), _ := λ n m f, ∃ k, misses k (` f).
Instance: ∀ (n:Object), LeftHereditary n (FFdD n).
Proof.
  intros ?????[x H].
  exists x.
  intro.
  apply_simplified H.
Qed.

Let iFF (n: Object) (c:n) : ∀ m f, (FF n c m f) → (FFdD n m f).
Proof. exists c. hyp_apply. Qed.

(* (δΔ n) m ⟶ {η : Nat (F:=Δ n) m | ∃ k,  *)
Definition δΔ (n: Object) := functors.object (F (P:=FFdD n)).
Definition ΛΔ (n: Object) (k: n) := functors.object (F (P:=FF n k)).

Definition i (n: Object) (k: n) (m: Object) := functors.arrow (ΛΔ n k) (δΔ n) (N (iFF n k)).
Definition i' (n: Object) (m: Object) := functors.arrow (δΔ n) (Δ n) N'.
End δΛΔ.

(*Remove Hints jections.Inverse_instance_0 jections.Inverse_instance_1 : typeclass_instances.*)

Definition BP := PowerSet ∘ orders.forget ∘ D.
Hint Unfold BP : typeclass_instances.


Instance: Fmap (Arrows0:=InducedArrow _ D) BP := _.
Instance: Functor BP _ := _. (* Here for speed. *)

(*
Section F.
Context {C D} (F: C→D) `{Functor C D F}.
Instance Fmap'': Fmap F (Arrows0:=dual.flipA) (Arrows1:=dual.flipA) := λ v w, fmap F (v:=w).
Instance: Functor F _ := _.
End F.*)

Definition sdΔ' n := (homFrom (BP n)) ∘ D.
Hint Unfold sdΔ' : typeclass_instances.
Instance: ∀ n: Object, Fmap (Arrows0:=dual.flipA) (sdΔ' n) := _.

Instance: ∀ n: Object, Functor (sdΔ' n) (Fmap_instance_1 n) := _.
Definition sdΔ (n: Object) := functors.object (sdΔ' n).

Program Definition x: ∀ v w (_:v⟶w), (sdΔ' v ⇛ sdΔ' w) := λ v w f z s k, _.
Next Obligation. (* FIXME: Give this as a term *)
apply (` s).
pose (fmap BP (v:=w) (w:=v) f).
exact (` a k).
Defined.
Next Obligation.
  unfold x_obligation_1.
  constructor; try typeclasses eauto.
  * constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
    intros ???.
    destruct s.
    set (fmap BP (v:=w) (w:=v) f).
    destruct a.
    simpl.
    rewrite H.
    reflexivity.
  * intros.
    destruct s.
    apply order_preserving; try assumption.
    intros ?[?[??]].
    simpl in *.
    exists x2.
    hyp_rewrite.
    intuition.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  repeat intro.
  simpl.
  unfold x_obligation_1.
  apply H.
  set (fmap BP (v:=w) (w:=v) f).
  destruct a.
  simpl.
  rewrite H0.
  reflexivity.
Qed.

Instance: ∀ v w f, NaturalTransformation (x v w f).
Proof.
  repeat intro.
  destruct x1, y0; do 7 red in H; simpl in *.
  unfold compose.
  red in H0.
  set (fmap D f0).
  destruct a.
  simpl.
  rewrite (H _); [| reflexivity].
  destruct o1 as [[]].
  apply sm_proper.
  destruct o0 as [[]].
  apply sm_proper.
  do 3 red; simpl.
  split; intros [a [Ha Ha']]; exists a;
    [ rewrite (H0 a _ eq_refl) in Ha'; rewrite H1 in Ha
    | rewrite <- (H0 a _ eq_refl) in Ha'; rewrite <- H1 in Ha]; auto.
Qed.

Program Instance: Fmap sdΔ := λ v w f, functors.arrow (sdΔ v) (sdΔ w) (x v w f) _.

Instance: Functor sdΔ _ := {}.
Proof.
- intros.
  constructor; try typeclasses eauto.
  repeat intro.
  simpl.
  apply H0.
  split; simpl;
  intros [a0 [Ha Ha']]; exists a0;
  [ rewrite H2 in Ha;
    split; [ rewrite <- Ha; symmetry; apply H; reflexivity | rewrite <- (H1 a0)]
  | rewrite <- H2 in Ha;
    split; [ rewrite <- Ha; apply H; reflexivity | rewrite (H1 a0)]
  ]; intuition.
- repeat intro.
  simpl.
  unfold id.
  unfold x_obligation_1.
  simpl.
  rewrite <- (H y0 _ (reflexivity _)).
  destruct x1.  destruct o as [[]].
  apply sm_proper.
  split; simpl.
  * intros [a0 [Ha Ha']].
    rewrite <- (H0 a0 y1); [| transitivity x3]; assumption.
  * intro. exists x3.
    split; [ reflexivity
           | rewrite (H0 _ _ H1); assumption ].
- repeat intro.
  simpl.
  unfold x_obligation_1.
  apply H.
  clear x2 y0 H.
  split; simpl.
  * intros [a [Ha Ha']].
    rewrite (H0 a _ (reflexivity _)) in Ha'.
    eexists.
    split; [| exists a; split; [reflexivity | assumption]].
    rewrite <- H, <- Ha.
    reflexivity.
  * intros [a [Ha [b [Hb Hb']]]].
    exists b.
    split.
    rewrite H, <- Ha.
    unfold compose.
    destruct g. destruct o as [[]].
    simpl in *.
    apply sm_proper.
    exact Hb.
    rewrite (H0 b) by reflexivity.
   assumption.
Qed.

Definition sdΔ'' := functors.object (Arrows1:=functors.Arrow) sdΔ _.

Definition Ex X (m: Object) : setoids.Object := homTo X (sdΔ'' m).
Print Ex.

Section K.
Let K := λ X v w (f: w⟶v), (r (sdΔ'' v) (fmap sdΔ f)) X.
Obligation Tactic := idtac.
Global Program Instance: Fmap (Arrows0:=dual.flipA) (Ex X) := λ X v w f, exist Setoid_Morphism (K X v w f) _.
Next Obligation.
  intros.
  constructor.
  - typeclasses eauto.
  - typeclasses eauto.
  - repeat intro.
    apply (H x1).
    repeat intro.
    apply H0.
    split; simpl;
      intros [a [Ha Ha']]; exists a;
        [ rewrite (H1 a a) in Ha' by reflexivity; rewrite Ha
          | rewrite <- (H1 a a) in Ha' by reflexivity; rewrite Ha, H2 ];
        intuition.
Qed.
End K.

Instance: Functor (Ex X) _ := {}.
Proof.
  constructor; try typeclasses eauto.
  - repeat intro.
    apply (H0 x2).
    repeat intro.
    simpl.
    unfold x_obligation_1.
    apply H1.
    split; simpl;
    intros [k [Hk Hk']]; exists k;
    [ rewrite (H2 k) in Hk' by reflexivity;
      rewrite H3 in Hk;
      rewrite <- Hk;
      split; [ symmetry; apply (H k k (reflexivity _)) | assumption ]
    | rewrite <- (H2 k) in Hk' by reflexivity;
      rewrite <- H3 in Hk;
      rewrite <- Hk;
      split; [ apply (H k k (reflexivity _)) | assumption ]
    ].
- repeat intro.
  apply H.
  repeat intro.
  simpl.
  apply H0.
  split; simpl.
  * intros [k [Hk Hk']].
    rewrite <- (H1 k y2) by (transitivity x4; assumption).
    assumption.
  * intro.
    eexists.
    split; [| apply (H1 _ _ H2)]; auto.
- repeat intro.
  simpl.
  apply (H x2).
  repeat intro.
  apply H0.
  split; simpl.
  * intros [a [Ha Ha']].
    eexists. split.
    + rewrite <- H2, <- Ha.
      reflexivity.
    + exists a.
      split. reflexivity.
      rewrite <-(H1 a) by reflexivity; assumption.
  * intros [a [Ha [b [Hb Hb']]]].
    exists b.
    split.
    + rewrite H2, <- Ha.
      unfold compose.
      destruct f; destruct o as [[]].
      simpl.
      apply sm_proper.
      apply Hb.
    + rewrite (H1 b) by reflexivity; assumption.
Qed.
