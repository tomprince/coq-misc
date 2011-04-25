Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra.
(* me *)

Section Cross.
 Context `(Category L) `(Category R).

Inductive Object :=
| inl : L -> Object
| inr : R -> Object
| cross
.

Definition Arrow (x y: Object) : Type := match x, y with
    | inl l, inl r => l ⟶ r
    | inr l, inr r => l ⟶ r
    | inl _, _ => unit
    | _, inr _ => unit
    | cross, cross => unit
    | _, _ => Empty_set
end.

Global Instance: Arrows Object := Arrow.

Section contents.
Section more_arrows. Context (x y: Object).
    Global Instance e: Equiv (x ⟶ y) :=
      match x, y with
        | inl l, inl r => fun f g: l ⟶ r => f = g
        | inr l, inr r => fun f g: l ⟶ r => f = g
        | _, _ => fun _ _ => True
      end.

    Let e_refl: Reflexive e.
    Proof.
      intro f.
      unfold e.
      destruct x, y; reflexivity.
    Qed.

    Let e_sym: Symmetric e.
    Proof.
      clear e_refl.
      unfold e.
      intros f g.
      destruct x, y; try symmetry; trivial.
    Qed.

    Let e_trans: Transitive e.
    Proof.
      clear e_refl e_sym.
      intros f g h . unfold e.
      destruct x, y; try transitivity g; trivial.
    Qed.
    Instance: Equivalence e.
    Global Instance: Setoid (x⟶y).
  End more_arrows.

    Global Instance: CatId Object.
    Proof.
      intro x; destruct x; compute; exact cat_id || exact tt.
    Defined.

    Global Instance: CatComp Object.
      intros x y z; destruct x, y, z; compute; trivial;
        try contradiction; apply comp.
    Defined.

    Let id_l' (x y: Object) (f: x ⟶ y): cat_id ◎ f = f.
    Proof.
      destruct x, y; compute; trivial; apply id_l.
    Qed.
    Let id_r' (x y: Object) (f: x ⟶ y): f ◎ cat_id = f.
    Proof.
      destruct x, y; compute; trivial; apply id_r.
    Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      destruct w, x, y, z; compute; trivial; try contradiction; apply comp_assoc.
    Qed.
  End comp_assoc.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros x y z; destruct x, y, z; compute; trivial; try contradiction; [apply H0 | apply H2].
  Qed.

  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.

End contents.

End Cross.
