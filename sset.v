Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra setoid.

(* me *)

Require Import extra_tactics.

Set Implicit Arguments.

Require Import Program.

Definition Object := nat.
Definition D (n:nat) :=  {x: nat | x < n}.
Coercion D: nat >-> Sortclass.
Instance: ∀ n, Equiv (D n) := fun n x y => `x ≡ `y.
Instance: Setoid (D n).
Definition Arrow (M N: Object) := {f : M → N | (forall x y, le (`x)  (`y) → le (` (f x))  (` (f y)))}.

Hint Extern 4 (Arrows Object) => exact Arrow : typeclass_instances.
Section e. Context {M N: Object}.
  Section D.
    Global Instance: ∀ f: Arrow M N, Setoid_Morphism (`f).
    Proof.
      constructor; try typeclasses eauto.
      destruct f as [f Hf]; simpl in *.
      intros [x?][y?]?; simpl in *.
      unfold equiv, Equiv_instance_0 in H; simpl in H.
      Require Import Le.
      apply le_antisym; apply Hf; simpl
        ; rewrite H; apply le_refl.
    Qed.
  End D.
  Global Instance e: Equiv (M⟶N) := fun f g => ∀ x:M, `f x = `g x.
  Instance: Equivalence e.
  Proof. prove_equivalence. Qed.
  Global Instance: Setoid (M⟶N).
End e.


Global Program Instance: CatId Object := fun m => id.
Global Program Instance: CatComp Object := fun m n o f g => (compose f g).
Next Obligation.
  destruct f as [f Hf], g as [g Hg]; simpl.
  unfold compose; apply Hf, Hg; simpl.
  assumption.
Qed.

Global Instance: ∀ x y z: Object,
    Proper (equiv ==> equiv ==> equiv) ((◎): (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
Proof.
  intros m n o.
  unfold comp, CatComp_instance_0, equiv, e, compose.
  intros f f' Hf g g' Hg x; simpl.
  rewrite Hg; apply Hf.
Qed.

Let id_l' (x y: Object) (f: x⟶y): cat_id ◎ f = f.
Proof. intro; reflexivity. Qed.
Let id_r' (x y: Object) (f: x⟶y): f ◎ cat_id = f.
Proof. intro; reflexivity. Qed.
Let comp_assoc' (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z): c ◎ (b ◎ a) = (c ◎ b) ◎ a.
Proof. intro; reflexivity. Qed.

Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.
