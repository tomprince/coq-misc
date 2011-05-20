Set Automatic Coercions Import.
Require Import
   Morphisms RelationClasses Equivalence Setoid Arith
   abstract_algebra util canonical_names orders interfaces.orders.
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
Require Import theory.setoids.
Require Import orders.maps.
Require categories.order.
Require functor.

Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.

Section Delta.

(* Universe Hacks *)(*
Open Scope nat_scope.
Instance: Equiv nat := eq.
Program Instance: Equivalence (@eq nat).*)

Section induced_category.
Context `{Category C} B (F: B → C).
Instance InducedArrow: Arrows B := λ x y, F x ⟶ F y.
Global Instance: CatId B := λ x, cat_id : F x ⟶ F x.
Global Instance: CatComp B := λ x y z, comp (F x) (F y) (F z).
Global Instance: Category B.
Proof. constructor; unfold "⟶", InducedArrow, comp, CatComp_instance_0, cat_id, CatId_instance_0; try typeclasses eauto. Qed.

Global Instance: Fmap F := λ _ _,id.
Global Program  Instance: Functor F _.
End induced_category.

Inductive Object : Set := {D'' :> nat}.
Coercion Build_Object: nat >-> Object.
Definition D' (n:Object) :=  {x: nat | x ≤ n}.
Coercion D': Object >-> Sortclass.

Existing Instances sig_equiv po_setoid.
Section induced_order.
Context O `{PartialOrder O} (P : O → Prop).
Global Instance: Le (sig P) := λ x y, `x ≤ `y.
Global Instance: PartialOrder (A:=sig P) (≤).
Proof.
  constructor.
  typeclasses eauto.
  intros [][]? [][]?; split; intros ?; do 2 red in H0, H1; simpl in H0, H1; compute; [rewrite <-H0, <-H1 | rewrite H0, H1]; apply H2.
  constructor; auto.
  intros [][][]; compute; transitivity x0; auto.
  intros [][]; compute; intros. eapply (antisymmetry ); auto.
Qed.
End induced_order.

Definition D n := order.object (D' n).

Instance: Arrows Object := InducedArrow _ D.
Typeclasses Transparent Arrows Arrow.
 
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

Set Typeclasses Debug.
Global Instance: CatComp Object := _.
Global Instance: CatId Object := _.
Global Instance: Category Object := _.
Require categories.dual.

(* FIXME FIXME *)
Definition Δ (n: Object) := functor.object (Arrows0:=dual.flipA) (homFrom (Arrows0:=@dual.flipA _ Arrows_instance_0) n)  _ _.

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
  simpl.
  apply comp_proper; reflexivity || assumption.
Qed.
Global Instance: Functor F Fmap' := {}.
Proof.
  * intros ?[x p][y q] Hxy. do 4 red  in Hxy; simpl in Hxy. compute. rewrite Hxy. apply right_identity.
  * repeat intro. compute. do 4 red in H1; simpl in H1. rewrite H1. apply comp_assoc.
Qed.
Program Definition N' : F ⇛ (homTo c) := λ a (x: F a), proj1_sig (P:=P a) x.
Global Instance: NaturalTransformation N'.
Proof.
  intros ???[][]?.
  simpl. 
  unfold compose.
  do 4 red in H1.
  rewrite <-H1.
  reflexivity.
Qed.

End hered_functor.

Section hered_nat.
Context `{Category C}.
Context `{!LeftHereditary c P}.
Context `{!LeftHereditary c Q}.
Context (HPQ : ∀ x f, P x f → Q x f).
Program Definition N : (F (P:=P)) ⇛ (F (P:=Q)) := λ a (x: F a), proj1_sig (P:=P a) x.
Global Instance: NaturalTransformation N.
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

Let iFF (n: Object) (c:n) : ∀ m f, (FF n c m f) → (FFdD n m f).
Proof. exists c. hyp_apply. Qed.

(* (δΔ n) m ⟶ {η : Nat (F:=Δ n) m | ∃ k,  *)
Definition δΔ (n: Object) := functor.object (F (P:=FFdD n)) Fmap' _.
Definition ΛΔ (n: Object) (k: n) := functor.object (F (P:=FF n k)) Fmap' _.

Definition i (n: Object) (k: n) (m: Object) := functor.arrow (ΛΔ n k) (δΔ n) (N (iFF n k)).
Definition i' (n: Object) (m: Object) := functor.arrow (δΔ n) (Δ n) N'. 

Instance: ∀ `{Equiv T}, Equiv (T → Prop) := λ _ _, ext_equiv.
Definition P (T: Type) `{Equiv T} := {f : T → Prop | Proper ((=)==>(=)) f}.
Instance: ∀ T `{Equiv T}, Le (P T) := λ T _ Q R, ∀ x, `Q x → `R x.

Instance (*FIXME*) Setoid_instance_2: ∀ T `{Setoid T}, Setoid (P T).
Proof.
  constructor; repeat intro.
  destruct x; auto.
  destruct x, y; rewrite H1, <-(H0 y0); reflexivity.
  destruct x, y, z; rewrite H2, (H0 y0), (H1 y0); reflexivity.
Qed.
Instance: ∀ T `{Setoid T}, PartialOrder (_: Le (P T)).
Proof.
  constructor.
  * typeclasses eauto.
  * repeat intro; split; repeat intro; [rewrite <-(H1 x1) | rewrite (H1 x1)]; try reflexivity;
    apply H2; [rewrite (H0 x1) | rewrite <-(H0 x1)]; try reflexivity; assumption.
  * constructor; repeat intro; repeat hyp_apply.
  * constructor; intro; [apply H0 | apply H1]; destruct x,y; [rewrite <-H2 | rewrite H2]; assumption.
Qed.

Let PowerSet : setoid.Object → order.Object := λ x, order.object (P (setoid.T x)).
Program Instance: Fmap PowerSet := λ x y f p (b:y), ∃ a: x, (setoid.e y) (`f a) b ∧ p a.
Next Obligation.
  (* FIXME *) fold (@equiv _ (setoid.e y)).
  repeat intro.
  split; intros [a ?]; exists a; [ rewrite <-H | rewrite H ]; assumption.
Qed.
Next Obligation.
  (* FIXME *) fold (@equiv _ (setoid.e y)).
  constructor; try typeclasses eauto.
  * constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
    split; intros [a ?]; exists a;
      [ rewrite <-H0, <-(H a) | rewrite H0, (H a) ]; try reflexivity; try assumption.
  * intros [??][??] ? ?.
    intros [a [??]]; exists a; auto.
Qed.
Instance: Functor PowerSet _ := {}.
Proof.
  * constructor; try typeclasses eauto.
    repeat intro.
    split; intros [z ?]; exists z; [ rewrite <-H1, <-(H0 z) | rewrite H1, (H0 z) ];
    try reflexivity; split; [rewrite <-(H z z (reflexivity _)) | | rewrite (H z z (reflexivity _)) | ]; apply H2.
  * repeat intro. simpl.
    split.
    - intros [z ?].
      destruct H1, x.
      rewrite <-(H y0 _ (reflexivity _)), <-H0, <-H1.
      assumption.
    - intro; exists x0; split;
      [reflexivity | rewrite (H x0 y0 H0); assumption ].
  * repeat intro. simpl.
    unfold compose.
    split; intros [k ?].
     - exists (`g k). rewrite <-H0. split; try apply H1.
        exists k. split; try reflexivity.
        rewrite <-(H _ _ (reflexivity k)). apply H1.
     - destruct H1 as [? [l ?]].
       exists l.
       split. rewrite H0.
       destruct H2, f. rewrite H2. assumption.
       rewrite (H _ _ (reflexivity l)). apply H2.
Qed.

Remove Hints jections.Inverse_instance_0 jections.Inverse_instance_1 : typeclass_instances.
Definition BP (n: Object) := order.object (P n).
Program Instance: Fmap BP := λ x y f, fmap PowerSet (v:=setoid.object (D' x) _ _) f.
Next Obligation.
  destruct f, X.
  exists (` (fmap PowerSet (v:=setoid.object (D' x) _ _) (w:=setoid.object (D' y) _ _) (exist Setoid_Morphism x0 _))).
  simpl in x0.
  pose (compose x1 x0).
  pose (fmap (v:=D x)(w:=D y) PowerSet f).
red.

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
