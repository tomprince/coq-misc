Require Import
   Morphisms RelationClasses Equivalence Setoid Arith
   abstract_algebra setoid.

(* me *)

Require Import extra_tactics.

Set Implicit Arguments.

Require Import Program. 
Require peano_naturals.

Definition Object := nat.
Definition Δ (n:nat) :=  {x: nat | x < n}.
Coercion Δ: nat >-> Sortclass.
Instance: ∀ n, Equiv (Δ n) := λ n x y, `x ≡ `y.
Instance: Setoid (Δ n).
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

Global Instance: ∀ x y: Object, LeftIdentity ((◎):_→_→x⟶y) cat_id.
Proof. intros ????; reflexivity. Qed.
Global Instance: ∀ x y: Object, RightIdentity ((◎): _→_→x⟶y) cat_id.
Proof. intros ????; reflexivity. Qed.
Let  comp_assoc' (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z): c ◎ (b ◎ a) = (c ◎ b) ◎ a.
Proof. intro; reflexivity. Qed.

Global Instance: Category Object := { comp_assoc := comp_assoc' }.
