Require Import
   Morphisms RelationClasses Equivalence Setoid Arith
   abstract_algebra setoid util.
(* me *)

Require Import extra_tactics.

Require Import Program. 
Require Import hom_functor.

Hint Extern 4  => solve [repeat intro; simpl in *; hyp_apply].
Hint Extern 10 => apply _.
Hint Extern 4 => constructor.

Section Delta.

(* Universe Hacks *)
Open Scope nat_scope.
Instance: Equiv nat := eq.
Program Instance: Equivalence (@eq nat).

Inductive Object := {D :> nat}.
Coercion Build_Object: nat >-> Object.
Definition D' (n:Object) :=  {x: nat | x < n}.
Coercion D': Object >-> Sortclass.
Instance: ∀ n, Equiv (D n) := λ n, sig_equiv (λ x, x < n).
Instance: Setoid (D' n) := λ n, sig_equivalence (λ x, x<n).
Definition Arrow (M N: Object) := {f : M → N | (∀ x y, le (`x)  (`y) → le (` (f x))  (` (f y)))}.
Hint Extern 4 (Arrows Object) => exact Arrow : typeclass_instances.

Section e. Context {M N: Object}.
  Section D.
    Global Instance: ∀ f: Arrow M N, Setoid_Morphism (`f).
    Proof.
      constructor; try typeclasses eauto.
      destruct f as [f Hf]; simpl in *.
      intros [x?][y?]?.
      apply le_antisym; hyp_apply; hyp_rewrite; auto with arith.
    Qed.
  End D.
  Global Instance e: Equiv (M⟶N) := λ f g, ∀ x:M, `f x = `g x.
  Instance: Equivalence e.
  Proof. prove_equivalence. Qed.
  Global Instance: Setoid (M⟶N).
End e.

Global Program Instance: CatId Object := λ _, id.
Global Program Instance: CatComp Object := λ _ _ _ f g, λ x, f (g x).
Next Obligation.
  unfold canonical_names.Arrow, Arrow in *.
  program_simpl.
Qed.

Global Instance: ∀ x y z: Object,
    Proper (equiv ==> equiv ==> equiv) ((◎): (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
Proof.
  intros ???.
  unfold comp, equiv, e.
  repeat intro; simpl.
  unfold compose.
  hyp_rewrite; hyp_apply.
Qed.

Global Instance: ∀ x y: Object, LeftIdentity (comp x _ y) cat_id.
Proof. intros ????; reflexivity. Qed.
Global Instance: ∀ x y: Object, RightIdentity (comp x _ y) cat_id.
Proof. intros ????; reflexivity. Qed.
Global Instance: ArrowsAssociative Object.
Proof. repeat intro; reflexivity. Qed.

Global Instance: Category Object.


Require Import interfaces.functors.
Hint Extern 4 (Arrows Object) => exact Arrow : typeclass_instances.
Definition Δ (n: Object) := homTo n.
(* (δΔ n) m ⟶ {η : Nat (F:=Δ n) m | ∃ k,  *)
Definition dD (n m: Object) := {η: m⟶n | ∃ k: n, ∀ k', ¬ ` η k' = k  }.

Program Definition δΔ (n m:Object) := setoid.object (dD n m) _ _.
Require Import categories.
Program Definition HH (n v w: Object) (X: v⟶w) : δΔ n w → δΔ n v := λ a, exist _ (` a ◎ X) _. 
Next Obligation.
destruct a as [?[c ?]].
exists c.
auto.
Qed.
Definition i' n a: δΔ n a → Δ n a := λ X,  (` X).

Program Instance: Setoid_Morphism (i' n m).

Program Let HH' n w v (X:v⟶w) (Y:δΔ n w) : δΔ n v  := exist _ (`Y ◎ X) _. (* FIXME: Program Bug? *)
Next Obligation.
  destruct X, Y as [? [k ?]].
  simpl in *.
  exists k; auto.
Qed.

Program Instance: Fmap (Arrows0:= flip (_:Arrows _)) (δΔ n) := HH'.
 
Program Definition i n: (δΔ n) ⇛ Δ n := λ a, i' n a.
Program Instance: NaturalTransformation (Arrows0:=flip (_:Arrows _)) (F:=δΔ n) (i n).

Definition hD (n: Object) (k: n) (m: Object) := {η: m⟶n | ∀ k', ¬ ` η k' = k  }.
Program Definition Λ n k m := setoid.object (hD n k m) _ _.
Program Definition ΛHH n k v w (X: v⟶w) : Λ n k w → Λ n k v := λ a, exist _ (` a ◎ X) _. 
Next Obligation.
  destruct a as [a H].
  auto.
Qed.

Program Definition Λi' n k a: Λ n k a → δΔ n a := λ X, exist _ (` X) _.
Next Obligation.
  exists k; destruct X; auto.
Qed.

Program Instance: Setoid_Morphism (Λi' n k m).

Program Let ΛHH' n k w v (X:v⟶w) (Y:Λ n k w) : δΔ n v  := exist _ (`Y ◎ X) _. (* FIXME: Program Bug? *)
Next Obligation.
  exists k; destruct Y; auto.
Qed.

Program Instance: Fmap (Arrows0:= flip (_:Arrows _)) (Λ n k) := ΛHH'.
Next Obligation.
  destruct x4 as [[]], x3; auto.
Qed.
Next Obligation.
  destruct x4 as [[]], x3; auto.
Qed.
 
Program Definition Λi n k: (Λ n k) ⇛ δΔ n := λ a, i' n a.
Solve All Obligations using program_simpl; (try (exists k); try destruct x as [[]]; auto). 

Program Instance: NaturalTransformation (Arrows0:=flip (_:Arrows _)) (F:=Λ n k) (G:=δΔ n) (Λi n k).

Require Import theory.setoids.
Open Scope nat_scope.

Definition sdD (n m: Object) := { f : m →  (n → Prop) | (∀ x y: m, `x <= `y → ∀ z, f x z → f y z) /\ Proper ((=)==>(=)==>iff) f}.
Program Let sdΔ (n m: Object) := setoid.object (sdD n m) (sig_equiv _) _.
Next Obligation.
  unfold Setoid, equiv.
  constructor;
  repeat intro.
  destruct x as [x [? p]]; apply p; auto.
  symmetry; apply H; symmetry; auto.
  transitivity (` y x0 x1); [apply H| apply H0]; auto.
Qed.

Program Instance: ∀ n, Fmap (Arrows0:=flip (_:Arrows _)) (sdΔ n) := λ n v w f, exist _ (λ X: sdD n v, exist _ (λ x y, (` X (` f x) y)) _ ) _.
Next Obligation.
  split.
  intros. 
  destruct (proj2_sig X).
  apply (H1 (`f x)).
  apply (proj2_sig f x  y).
  assumption.
  assumption.
  repeat intro.
  destruct X as [X []].
  destruct f as [f ?].
  simpl in *.
  rewrite <-H0. 
  assert (f x = f y) by (apply le_antisym; hyp_apply; hyp_rewrite; auto with arith).
  rewrite H1.
  auto.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  apply (setoid.setoid_proof (sdΔ n v)).
  apply (setoid.setoid_proof (sdΔ n w)).
  intros [][]???????.  simpl in *.
  apply H; auto.
  destruct f.
  apply le_antisym; hyp_apply; hyp_rewrite; auto with arith.
Qed.

Program Instance: Functor (Arrows0:=flip (_:Arrows _)) (sdΔ n) _.
Next Obligation.
  constructor; try typeclasses eauto.
  intros [][]?[?[]][?[]]???????. simpl in *.
  apply H0.
  apply le_antisym; hyp_rewrite; hyp_apply; hyp_rewrite; auto.
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
  repeat apply sm_proper.
  auto.
Qed.

Require categories.functor.
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
  pose (fmap (Arrows0:=flip (_:Arrows _)) (sdΔ) X0).
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
