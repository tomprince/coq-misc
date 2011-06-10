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
Require Import hom_functor.
Set Inconsistent Universes.
Require Import peano_naturals.
Require Import theory.setoids.
Require Import orders.maps.
Require categories.order.

Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.

Require Import theory.left_hereditary.
Require Import theory.powerset.

Section Delta.

(* Universe Hacks *)(*
Open Scope nat_scope.
Instance: Equiv nat := eq.
Program Instance: Equivalence (@eq nat).*)

Require Import categories.induced.

Inductive Object : Set := {D'' :> nat}.
Coercion Build_Object: nat >-> Object.
Definition D' (n:Object) :=  {x: nat | x ≤ n}.
Coercion D': Object >-> Sortclass.

Existing Instances po_setoid.

Require Import order.induced.

Instance Equiv_instance_1: Equiv (D' n) := fun n => sig_equiv _.
Definition D n := @order.object (D' n) _ (induced.Le_instance_0 _ _ (@proj1_sig _ _ )) _ _.

 
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

Definition Δ (n: Object) := functors.object (homFrom n) _ _.
Print Δ.


Definition misses {A} `{Equiv B} x (f: A->B) := forall y, ~ f y = x.

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
Definition δΔ (n: Object) := functors.object (H:=dual.e) (F (P:=FFdD n)) Fmap' _.
Definition ΛΔ (n: Object) (k: n) := functors.object (F (P:=FF n k)) Fmap' _.

Definition i (n: Object) (k: n) (m: Object) := functors.arrow (ΛΔ n k) (δΔ n) (N (iFF n k)).
Definition i' (n: Object) (m: Object) := functors.arrow (δΔ n) (Δ n) N'.

Remove Hints jections.Inverse_instance_0 jections.Inverse_instance_1 : typeclass_instances.

Definition U (O: order.Object) : setoids.Object := setoids.object O _ _.
Typeclasses eauto := 5.
Program Instance: Fmap U := λ x y f, f.
Next Obligation.
  destruct f.
  auto.
Qed.

Instance: Functor U _ := {}.
Proof.
  * constructor; try typeclasses eauto.
    intros ???. assumption.
  * intros ????. assumption.
  * intros ??[] ?[] ???.
    simpl. rewrite H.
    reflexivity.
Qed.

Definition BP := PowerSet ∘ U ∘ D.
Instance: Fmap (Arrows0:=InducedArrow _ D) BP := _.
Proof.
  eapply comp_Fmap.
  eapply comp_Fmap.
  typeclasses eauto.
  typeclasses eauto.
  typeclasses eauto.
Defined.

Instance: Functor BP _ := _.

Section F.
Context {C D} (F: C→D) `{Functor C D F}.
Instance Fmap'': Fmap F (Arrows0:=dual.flipA) (Arrows1:=dual.flipA) := λ v w, fmap F (v:=w).
Instance: Functor F _ := _.
End F.

Definition sdΔ' n := compose (homTo (BP n)) D.
Instance: ∀ n: Object, Fmap (Arrows0:=dual.flipA) (Arrows1:=setoid.Arrow) (sdΔ' n) := {}.
Proof. eapply (comp_Fmap _ _ _ (g := D) (g' := Fmap'' _)). Defined.

Instance: ∀ n: Object, Functor (sdΔ' n) (Fmap_instance_2 n) := _.
Definition sdΔ (n: Object) := functor.object (Arrows0:=dual.flipA) (sdΔ' n) _ _.

Goal ∀ v w (_:v⟶w), (homTo (BP v) ⇛ homTo (BP w)).
intros.
unfold homFrom.
change (homFrom a (BP v) ⟶ homFrom a (BP w)).
apply fmap. typeclasses eauto.
apply fmap. apply Fmap''. typeclasses eauto.
exact X.
Check (r (BP w) (setoid.T (homFrom (BP v) (BP w)))).
unfold sdΔ'.
red. red.

Program Instance: Fmap sdΔ := λ _ _ X, functor.arrow _ _ _ _.
Next Obligation.
Qed.
intros ???.
red. red. 
Eval lazy [Inverse Nat] in proj2_sig (r (BP w) v).
refine (functor.arrow (sdΔ v) (sdΔ w) (r X)).
apply (proj2_sig (P:=NaturalTransformation)).


unfold sdΔ. 

Program Definition sdΔ'' := functor.object (Arrows1:=functor.Arrow) sdΔ _ _.

(* FIXME: The term should be broken up. *)
Program Definition sdΔ'' := functor.object (Arrows1:=functor.Arrow) sdΔ (λ n m (f: n⟶m), functor.arrow (sdΔ n) (sdΔ m) (λ (v: Object) (X: sdD n v), λ (v0:v) (y:m), ∃ x:n, `f x = y ∧ X v0 x) _) _.
Next Obligation.
  repeat (constructor; try typeclasses eauto).
  * intros [x' [Hx ?]].
    exists x'. destruct f, X. simpl in *.
    split; try assumption.
    rewrite (sm_proper (f:=x2) y x (symmetry H) x'); assumption.
  * intros [x' [? ?]].
    exists x'. destruct f, X. simpl in *.
    split; try assumption.
    rewrite (sm_proper (f:=x2) x y H x'); assumption.
  * intros ???? [x' [??]].
    exists x'.
    destruct f, X; simpl in *.
    split; try assumption.
    apply (order_preserving x2 x y H x').
    assumption.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  eapply (setoid.setoid_proof (sdΔ' n v)).
  eapply (setoid.setoid_proof (sdΔ' m v)).
  intros ??? ??? ?; simpl in *.
  cut (∀ (x y: sdD n v) (_:x=y) x0 y0 (_:x0=y0), (∃ v0: n, `f v0 = x1 ∧ (`x x0 v0)) → (∃ v0: n, `f v0 = x1 ∧ (`y y0 v0))); [split; apply H1; assumption || symmetry; assumption|].
  intros. destruct H3 as [h h']; exists h. destruct x2,y1; do 2 red in H1; simpl in *. rewrite <- (H1 _ _  H2 h). assumption.
Qed.
Next Obligation.
  repeat intro. simpl in *.
  split; intro; destruct f0; pose (order_morphism_mor x3);
    destruct H1 as [h [h'? ]]; exists h; (split; [assumption|]);
    pose proof H (x3 x1) (x3 y1) (sm_proper (f:=x3) x1 y1 H0) h as R.
  * rewrite <-R; assumption.
  * rewrite R; assumption.
Qed.
Next Obligation.
constructor; try typeclasses eauto.
* constructor; try typeclasses eauto.
  intros ??? ? ??? ??? ?. simpl in *.
  split; intros [h ?]; exists h;
    pose proof (H h) as R1;
    destruct y0 as [y0 ?];
    pose proof (order_morphism_mor y0);
      pose proof H0 x2 y1 H1 h as R2.
  - rewrite <-R1, <-R2. assumption.
  - rewrite R1, R2. assumption.
* repeat intro.
  simpl in *. unfold id.
  split; intro.
  - destruct H1 as [?[??]].
   rewrite <-(H x1 y0 H0 x2).
   clear H y0 H0.
   Set Typeclasses Debug.
   destruct x0.
   pose proof (order_morphism_mor x0).
   simpl.
   erewrite (sm_proper (f:=x0) (x1) (x1)).
   destruct (functor_morphism (sdΔ' a)).
   pose proof (sm_proper (`x0 x1)).
    simpl.
    Check (x0 x1).
    pose (order_morphism_mor (x0 x1)).
    rewrite <- H1.

Qed.

End Delta.
(*
Program Instance: ∀ n, Fmap (Arrows0:=flip (_:Arrows _)) (sdΔ n) := λ n v w f, exist _ (λ X: sdD n v, exist _ (λ x y, (` X (` f x) y)) _ ) _.
Next Obligation.
  constructor.
  constructor.
  * constructor; try typeclasses eauto.
    repeat intro.
    destruct X, f. simpl in *.
    pose proof (order_morphism_mor x1).
    pose proof (order_morphism_mor x2).
    apply (@sm_proper _ _ _ _ _ H0).
    apply (@sm_proper _ _ _ _ _ H1).
    assumption.
  * repeat intro.
    unfold Order_instance_0.
    do 2 red in H, H0.
    rewrite H, H0.
    auto.
  * repeat intro.
    unfold Order_instance_1.
    split; repeat intro;
    symmetry in H0; repeat hyp_apply.
  * intros.
    apply order_preserving; [apply (proj2_sig _)|].
    apply order_preserving; [apply (proj2_sig _)|].
    assumption.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  apply (setoid.setoid_proof (sdΔ n v)).
  apply (setoid.setoid_proof (sdΔ n w)).
  intros [][]?????; simpl in *.
  apply H; auto.
  destruct f.
  pose proof (order_morphism_mor x3).
  apply (@sm_proper _ _ _ _ _ H1).
  assumption.
Qed.

Program Instance: Functor (Arrows0:=flip (_:Arrows _)) (sdΔ n) _.
Next Obligation.
  constructor; try typeclasses eauto.
  intros [][]?[?[]][?[]]?????. simpl in *.
  apply H0.
  rewrite (H x3).
  simpl.
  pose proof (order_morphism_mor x0).
  apply (@sm_proper _ _ _ _ _ H2).
  assumption.
Qed.
Next Obligation.
  repeat intro.
  apply H; auto.
Qed.
Next Obligation.
  repeat intro.
  simpl in *.
  apply H; auto.
  unfold compose.
  repeat apply sm_proper.
  auto.
Qed.

Let Ex (X: functor.Object Object (Arrows0:=flip (_:Arrows _)) setoid.Object) (m: Object) : setoid.Object := homTo X (functor.object (sdΔ m) _ _).
Program Instance: Fmap (Arrows0:=flip (_:Arrows _)) (Ex X).
Next Obligation.
  eexists.
  assert (Ex X v → Ex X w).
  intros [eta Heta].
  econstructor.
  assert (functor.map_obj
        {|
        functor.map_obj := sdΔ w;
        functor.Fmap_inst := Fmap_instance_2 w;
        functor.Functor_inst := Functor_instance_0 |} ⇛ functor.map_obj X).
  intro.
  econstructor.
  assert (functor.map_obj
        {|
        functor.map_obj := sdΔ w;
        functor.Fmap_inst := Fmap_instance_2 w;
        functor.Functor_inst := Functor_instance_0 |} a
      → functor.map_obj X a).
  intro.
  destruct X as [X Xmap ?].
  simpl in *.
  do 2 red in X0.
  pose (fmap (Fmap:=Fmap_instance_2) (Arrows0:=flip (_:Arrows _)) (sdΔ) X0).
  assert (sdD v v).
  red.
  exists (λ x y: v, `y < `x); split.
  * intros. eapply lt_le_trans; hyp_apply.
  * repeat intro. repeat hyp_rewrite. auto.
*  
  pose (Heta v w X0 X2 X2 (reflexivity _)).
  simpl in *; unfold compose in *.
  apply (` (eta a)).
  unfold sdΔ in *; simpl in *.
  unfold sdD.
  simpl.
  destruct X0 as [X0 []].
*)
