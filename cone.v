Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra functors.
(* me *)

Section Cross.
Context `(Category J) `(Category C) `{!Functor (X:J->C) X'}.

Class Cone (c:C) (f:forall j:J, c ⟶ X j) := cone :
  forall (j j': J) (a:j⟶j'), (fmap X a) ◎ f j = f j'. 

Class ConeMorphisms `(Cone c f) `(Cone c' f') (mu: c ⟶ c') := cone_morphism :
  forall j:J, f' j ◎ mu = f j.

Record Object := object { 
  vertex :> C;
  legs :> forall j:J, vertex ⟶ X j;
  cone_inst :> Cone vertex legs
}.

Record Arrow (x y: Object) : Type := arrow {
  mor :> vertex x ⟶ vertex y;
  cone_mor_inst :> ConeMorphisms (cone_inst x) (cone_inst y) mor
}.
Implicit Arguments mor [[x] [y]].

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typclasses_instance.

Section contents.
Section more_arrows. Context (x y: Object).
    Global Instance e: Equiv (x ⟶ y) := fun f g => mor f = mor g.

    Let e_refl: Reflexive e.
    Proof.
      intro f; unfold e; reflexivity.
    Qed.

    Let e_sym: Symmetric e.
    Proof.
      intros f g; unfold e; symmetry; trivial.
    Qed.

    Let e_trans: Transitive e.
    Proof. intros f g h; unfold e; intros Hfg Hgh; rewrite Hfg, Hgh; reflexivity. Qed.
    Instance: Equivalence e.
    Global Instance: Setoid (x⟶y).
  End more_arrows.

    Global Instance: CatId Object.
    Proof.
      intros x.
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
