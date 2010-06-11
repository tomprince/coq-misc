Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra.
(* me *)

Section Join.
 Context `(Category L) `(Category R).

Definition Object : Type := sum L R.

Definition Arrow (x y: Object) := match x, y with
    | inl l, inl r => l ⟶ r
    | inl l, inr r => unit
    | inr l, inr r => l ⟶ r
    | inr l, inl r => Empty_set
end.

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typclasses_instance.

Section contents.
Section more_arrows. Context (x y: Object).
    Global Instance e: Equiv (x ⟶ y).
    Proof.
      destruct x; destruct y; intros f g; do 3 red in f, g.
      - exact (f = g).
      - exact (eq tt tt).
      - case f.
      - exact (f = g).
    Defined.
End more_arrows. (* end this, since we need to destruct x & y *)

    Let e_refl (x y: Object): Reflexive (e x y).
    Proof.
      intro f. red.
      destruct x; destruct y; try reflexivity.
      contradiction.
    Qed.

    Let e_sym (x y: Object): Symmetric (e x y).
    Proof.
      destruct x, y; intros f g; unfold e.
      - symmetry; assumption.
      - intros; assumption.
      - intros; contradiction.
      - symmetry; assumption.
    Qed.

    Let e_trans (x y: Object): Transitive (e x y).
    Proof.
      destruct x, y; intros f g h; unfold e; intros Hfg Hgh.
      - transitivity g; assumption.
      - apply refl_equal.
      - contradiction.
      - transitivity g; assumption.
    Qed.
    Instance: forall x y: Object, Equivalence (e x y).
    intros x y; split; apply _.
    Defined.
    Global Instance: forall x y: Object, Setoid (x⟶y).
      intros x y. red. apply _.
    Defined.

    Global Instance: CatId Object.
    Proof.
      intro x; destruct x; do 3 red; exact cat_id.
    Defined.

    Global Instance: CatComp Object.
      intros x y z. destruct x, y, z; unfold canonical_names.Arrow, Arrows_instance_0, Arrow; try exact comp; try (intros; apply tt); try contradiction.
    Defined.

    Let id_l' (x y: Object) (f: x ⟶ y): cat_id ◎ f = f.
    Proof.
      destruct x, y; unfold comp; unfold CatComp_instance_0;
      do 3 red in f;
      unfold comp;
      unfold Arrow; unfold e; red; unfold cat_id; unfold CatId_instance_0;
      try apply id_l.
      apply refl_equal.
      contradiction.
    Qed.
    Let id_r' (x y: Object) (f: x ⟶ y): f ◎ cat_id = f.
    Proof.
      destruct x, y;
      unfold comp, CatComp_instance_0, comp;
      unfold e, Arrow, cat_id, CatId_instance_0;
      try apply id_r.
      apply refl_equal.
      contradiction.
    Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      destruct w, x, y, z;
      unfold comp, Arrow, e, CatComp_instance_0;
      try apply comp_assoc;
      try apply refl_equal;
      try contradiction.
    Qed.
  End comp_assoc.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros x y z; destruct x, y, z;
    unfold comp, CatComp_instance_0;
    try (intros ? ? ? ? ? ?; reflexivity);
    try (intros ? ? ? ? ? ?; contradiction).
    apply H0. apply H2.
  Qed.

  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.

End contents.
