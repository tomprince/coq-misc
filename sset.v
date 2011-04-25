Require Import
   Morphisms RelationClasses Equivalence Setoid Arith
   abstract_algebra util.
Set Automatic Coercions Import.
Require setoid.
(* me *)

Require Import interfaces.functors.
Require Import extra_tactics.
Require Import theory.categories.
Require categories.functor.

Require Import Program. 
Require Import hom_functor.
Set Inconsistent Universes.
Require Import peano_naturals.

Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.

Section Delta.

(* Universe Hacks *)(*
Open Scope nat_scope.
Instance: Equiv nat := eq.
Program Instance: Equivalence (@eq nat).*)

Inductive Object : Set := {D :> nat}.
Coercion Build_Object: nat >-> Object.
Definition D' (n:Object) :=  {x: nat | x ≤ n}.
Coercion D': Object >-> Sortclass.

Instance: ∀ n: nat, Order (Build_Object n) := λ _ x y, (`x) ≤ (`y).
Instance: ∀ n: nat, @PartialOrder (Build_Object n) _ _.
Proof.
  constructor.
  typeclasses eauto.
  intros [][]? [][]?; split; intros ?; do 2 red in H, H0; simpl in H, H0; compute; [rewrite <-H, <-H0| rewrite H, H0]; apply H1.
  constructor; auto.
  intros [][][]; compute; transitivity x0; auto.
  intros [][]; compute; intros; apply le_antisym; auto.
Qed.
Instance: ∀ n: nat, Setoid (Build_Object n) := {}.
Definition Arrow := fun (N M: Object) => (sig (OrderPreserving (A:=N) (B:=M)): Set). 
Hint Extern 4 (Arrows Object) => exact Arrow : typeclass_instances.
Typeclasses Transparent Arrows Arrow.
 
Section ord.
  Context `{PartialOrder A} `{PartialOrder B} `{!OrderPreserving  (f: A→B)}.
  Global Instance HHH : Proper ((=) ==> (=)) f.
  Proof.
    intros a b Hab.
    pose proof (poset_setoid: Setoid A).
    apply (antisymmetry (≤));
      apply order_preserving; auto;
        eapply poset_proper; try apply Hab; try reflexivity.
  Qed.
End ord.

Require Import orders.maps.
Section e. Context {M N: Object}.
  Section D.
    Global Program Instance: ∀ f: Arrow M N, Setoid_Morphism (`f).
    Next Obligation.
      destruct f.
      apply HHH.
    Qed.
  End D.
  
  Global Instance e: Equiv (M ⟶ N) := λ f g, ∀ x:M, `f  x = `g x.
  Instance: Equivalence e.
  Proof. prove_equivalence. Qed.
  Global Instance: Setoid (M ⟶ N) := {}.
End e.

Global Program Instance: CatId Object := λ _, id.
Global Program Instance: CatComp Object := λ _ _ _ g f, (compose g f).
Next Obligation.
  unfold canonical_names.Arrow, Arrow in *.
  destruct f, g.
  eapply compose_order_preserving.
Qed.

Global Instance: ∀ x y z: Object,
    Proper (equiv ==> equiv ==> equiv) ((◎): (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
Proof.
  intros [][][]?.
  unfold comp, equiv, e.
  repeat intro; simpl.
  unfold compose.
  rewrite H0. apply H.
Qed.

Global Instance: ∀ x y: Object, LeftIdentity (comp x _ y) cat_id.
Proof. intros ????; reflexivity. Qed.
Global Instance: ∀ x y: Object, RightIdentity (comp x _ y) cat_id.
Proof. intros ????; reflexivity. Qed.
Global Instance: ArrowsAssociative Object.
Proof. repeat intro; reflexivity. Qed.

Global Instance: Category Object := {}.

Definition Δ (n: Object) := functor.object (Arrows0:=dual.flipA) (homTo n) _ _.

Definition misses {A} `{Equiv B} x (f: A->B) := forall y, ~ f y = x.

Section hered.
Context `{Category C} (c : C).
Class LeftHereditary (H: ∀ {x: C}, (x ⟶ c) → Prop) := left_hereditary : ∀ {x y:C} (f:x⟶c) (g:y⟶x), H f → H (f ◎ g).
End hered.
Implicit Arguments left_hereditary [[C] [Arrows0] [CatComp0] [c] [H] [LeftHereditary] [x] [y]].

Require Import workaround_tactics.
Section hered_functor.
Context `{Category C}.
Context `{LH: !LeftHereditary c P}.
(* CatComp0 is unfold due to a bug *)
Definition F := (λ x, setoid.object (sig (P x))  _ _).
Global Program Instance Fmap: Fmap (Arrows0:=dual.flipA) F
  := λ v w (X: w ⟶ v),  (λ f: {f: v ⟶ c | P v f}, (CatComp0 _ _ _ (`f) X) ↾ (left_hereditary (`f) X (proj2_sig f))).
Next Obligation.
constructor; try typeclasses eauto.
intros ???. compute.
apply comp_proper; reflexivity || assumption.
Qed.
Instance: ∀ a b, Setoid_Morphism (fmap F (v:=a) (w:=b)) := {}.
Proof.
  repeat intro.
  simpl.
  apply comp_proper; reflexivity || assumption.
Qed.
Global Instance: Functor F Fmap := {}.
Proof.
  * intros ?[x p][y q] Hxy. do 4 red  in Hxy; simpl in Hxy. compute. rewrite Hxy. apply right_identity.
  * repeat intro. compute. do 4 red in H1; simpl in H1. rewrite H1. apply comp_assoc.
Qed.

Program Definition N' : F ⇛ (homTo c) := λ a, λ x: F a, ` x .
Global Instance: NaturalTransformation (Arrows0:=dual.flipA) N'.
Proof.
  repeat intro; compute.
  apply comp_proper; reflexivity || assumption.
Qed.
End hered_functor.

Section hered_nat.
Context `{Category C}.
Context `{!LeftHereditary c P}.
Context `{!LeftHereditary c Q}.
Context (HPQ : ∀ x f, P x f → Q x f).
Program Definition N : (F (P:=P)) ⇛ (F (P:=Q)) := λ a (x: F a), proj1_sig (P:=P a) x.
Global Instance: NaturalTransformation (Arrows0:=dual.flipA) N.
Proof.
  intros ???[][]?.
  simpl. 
  unfold compose.
  apply comp_proper; reflexivity || assumption.
Qed.
End hered_nat.

Let FF:  forall n:Object, ∀ (c:n)(m:Object) (f: m ⟶ n), _ := λ C c x f, misses c (` f).
Instance: ∀ (n:Object) (c:n), LeftHereditary n (FF n c).
Proof.
  repeat intro.
  eapply H.
  apply_simplified H0.
Qed.

Let FFdD:  forall n:Object, ∀ (m:Object) (f: m ⟶ n), _ := λ n m f, ∃ k, misses k (` f).
Instance: ∀ (n:Object), LeftHereditary n (FFdD n).
Proof.
  intros ?????[x H].
  exists x.
  intro.
  apply_simplified H.
Qed.

Check N.
Let iFF (n: Object) (c:n) : ∀ m f, (FF n c m f) → (FFdD n m f).
Proof. exists c. hyp_apply. Qed.

(* (δΔ n) m ⟶ {η : Nat (F:=Δ n) m | ∃ k,  *)
Require functor.
Definition δΔ (n: Object) := functor.object (F (P:=FFdD n)) (Fmap) _.
Definition ΛΔ (n: Object) (k: n) := functor.object (F (P:=FF n k)) Fmap _.

Definition i (n: Object) (k: n) (m: Object) := functor.arrow (ΛΔ n k) (δΔ n) (N (iFF n k)).
Definition i' (n: Object) (m: Object) := functor.arrow (δΔ n) (Δ n) N'.


Instance: ∀ T, Order (T → Prop) := λ T P Q, ∀ x, P x → Q x.
Instance: ∀ T, Equiv (T → Prop) := λ T P Q, ∀ x, P x = Q x.
Instance: ∀ T, PartialOrder (_: Order (T → Prop)).
Proof.
  unfold Order_instance_1.
  constructor.
  * typeclasses eauto.
  * intros ??? ???; split; intros ???; repeat hyp_apply.
  * constructor; repeat intro; repeat hyp_apply.
  * repeat intro; split; hyp_apply.
Qed.
Definition sdD (n m: Object) := { f : m →  (n → Prop) | OrderPreserving f}.
Program Let sdΔ (n m: Object) := setoid.object (sdD n m) (sig_equiv _) _.
Next Obligation.
  unfold Setoid, equiv.
  constructor.
  * intro x; destruct x as [x[]].
    simpl.
    pose proof (order_morphism_mor x) as Hx.
    apply (@sm_proper _ _ _ _ _  Hx).
  * intros x y Hxy ???; symmetry; apply Hxy; symmetry; assumption.
  * intros ??? ?? ?.
    destruct x as [x[]], y as [y[]], z as [z[]].
    pose proof (order_morphism_mor x) as Hx.
    pose proof (order_morphism_mor y) as Hy.
    pose proof (order_morphism_mor z) as Hz.
    simpl in *.
    intros.
    rewrite (H x0); [ apply (H0 x0) ;  assumption |  reflexivity ].
Qed.

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
