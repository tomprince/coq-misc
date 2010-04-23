Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import abstract_algebra functors categories.
(* me *)

Set Automatic Introduction.

Hint Extern 4 => reflexivity.

Section Comma.
Context `{Category L} `{Category R} `{Category C}.
Context `{!Functor (l:L->C) l'} `{!Functor (r:R->C) r'}.

Record Object: Type := object {
  Lobj : L;
  Robj : R;
  Cmap : l Lobj ⟶ r Robj
}.

Record Arrow (x y : Object) : Type := arrow {
  Lmap : Lobj x ⟶ Lobj y;
  Rmap : Robj x ⟶ Robj y;
  Ccom : fmap r Rmap ◎ Cmap x = Cmap y ◎ fmap l Lmap
}.
Implicit Arguments Lmap [[x] [y]].
Implicit Arguments Rmap [[x] [y]].
Implicit Arguments arrow [[x] [y]].

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.

Section contents.
  Section more_arrows. Context (x y: Object).
    Global Program Instance e: Equiv (x ⟶ y) := fun f g =>
      Lmap f = Lmap g /\ Rmap f = Rmap g.

    Let e_refl: Reflexive e.
    Proof.
      intros f.
      split; reflexivity.
    Qed.

    Let e_sym: Symmetric e.
    Proof.
      intros ? ? [? ?]; split;
      hyp_rewrite; reflexivity.
    Qed.

    Let e_trans: Transitive e.
    Proof.
      intros ? ? ? [?  ?] [? ?].
      split; repeat hyp_rewrite; reflexivity.
    Qed.

    Instance: Equivalence e.
    Global Instance: Setoid (x ⟶ y).
  End more_arrows.


  Let id_com {x : Object} : fmap r cat_id ◎ Cmap x = Cmap x ◎ fmap l cat_id.
  Proof.
    rewrite preserves_id, preserves_id; try assumption.
    rewrite id_l, id_r; reflexivity.
  Qed.
  Global Program Instance: CatId Object := fun _ => arrow cat_id cat_id id_com.

  Let comp_com {x y z: Object} {f : Arrow x y} {g: Arrow y z}
    : fmap r (Rmap g ◎ Rmap f) ◎ Cmap x = Cmap z ◎ fmap l (Lmap g ◎ Lmap f).
  Proof.
    rewrite preserves_comp, preserves_comp; try assumption.
    rewrite <- comp_assoc, Ccom, comp_assoc, Ccom, comp_assoc.
    reflexivity.
  Qed.
  Global Instance: CatComp Object := fun _ _ _ f g => arrow (Lmap f ◎ Lmap g) (Rmap f ◎ Rmap g) comp_com.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros.
    intros ? ? [? ?].
    intros ? ? [? ?].
    split; simpl; repeat hyp_rewrite; reflexivity.
  Qed.

  Let id_l' (x y: Object) (f: x ⟶ y): cat_id ◎ f = f.
  Proof.
    split; simpl; apply id_l.
  Qed.
  Let id_r' (x y: Object) (f: x ⟶ y): f ◎ cat_id = f.
  Proof.
    split; simpl; apply id_r.
  Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      split; simpl; apply comp_assoc.
    Qed.
  End comp_assoc.
  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.
End contents.

End Comma.
