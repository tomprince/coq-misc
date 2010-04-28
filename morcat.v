Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra interfaces.functors theory.categories.
(* me *)
Require Import square.

Set Automatic Introduction.

Section MorCat.
Context `{Category A}.

Record Object: Type := object {
  initial: A;
  terminal: A;
  arr:> initial ⟶ terminal
}. 

Implicit Arguments object [[initial] [terminal]].


Record Arrow (i p: Object) : Type := arrow {
  top : initial i ⟶ initial p;
  bottom : terminal i ⟶ terminal p;
  sqaure : Square i p top bottom
}.
Implicit Arguments top [[i] [p]].
Implicit Arguments bottom [[i] [p]].
Implicit Arguments arrow [[i] [p]].

Global Existing Instance sqaure.
Global Instance: Arrows Object := Arrow.

Section contetns.
  Section more_arrows. Context (i p: Object).
    Global Program Instance e: Equiv (i ⟶ p) := fun sq sq' =>
      top sq = top sq' /\ bottom sq = bottom sq'.

    Let e_refl: Reflexive e.
    Proof. constructor; reflexivity. Qed.
    Let e_sym: Symmetric e.
    Proof. intros ? ? [? ?]; split; symmetry; trivial. Qed.
    Let e_trans: Transitive e.
    Proof. intros ? ? ? [? ?] [? ?]; split; repeat hyp_rewrite; reflexivity. Qed.

    Instance: Equivalence e.
    Global Instance: Setoid (i⟶p).
  End more_arrows.

  Global Instance: CatId Object := fun _ => arrow cat_id cat_id _.
  Global Instance: CatComp Object := fun _ _ _ m n => arrow ((top m) ◎ top n) (bottom m ◎ bottom n) _.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros.
    intros ? ? [? ?].
    intros ? ? [? ?].
    do 2 red; split; simpl; repeat hyp_rewrite; reflexivity.
    Qed.

  Let id_l' (x y: Object) (sq: x ⟶ y): cat_id ◎ sq = sq.
  Proof. do 2 red; split; simpl; apply id_l. Qed.

  Let id_r' (x y: Object) (sq: x ⟶ y): sq ◎ cat_id = sq.
  Proof. do 2 red; split; simpl; apply id_r. Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof. do 2 red; split; simpl; apply comp_assoc. Qed.
  End comp_assoc.
   
  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r' }.
End contetns.
End MorCat.
Coercion object: canonical_names.Arrow >-> Object.
