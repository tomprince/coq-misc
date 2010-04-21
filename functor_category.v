Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import abstract_algebra functors categories.
(* me *)
(*Require Import nattrans.*)

Hint Extern 4 => reflexivity.
Set Automatic Introduction.

Section FunCat.
Context `(Category A) `(Category B).

Record Object: Type := object {
  map_obj:> A->B;
  Fmap_inst:> Fmap map_obj;
  Functor_inst:> Functor map_obj _
}.
Implicit Arguments object [[Fmap_inst] [Functor_inst]].

Global Existing Instance Fmap_inst.
Global Existing Instance Functor_inst.

Record Arrow (F G : Object) : Type := arrow {
  eta:> map_obj F ⇛ map_obj G;
  NaturalTransformation_inst : NaturalTransformation eta
}.
Implicit Arguments arrow [[F] [G]].
Global Existing Instance NaturalTransformation_inst.
Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.

Section contents.
  Section more_arrows. Context (F G: Object).
    
    Global Program Instance e: Equiv (F ⟶ G) := fun m n =>
      forall x: A, m x = n x.

    Let e_refl: Reflexive e.
    Proof.
      intro a; red; reflexivity.
    Qed.

    Let e_sym: Symmetric e.
    Proof.
      intros m n Hmn.
      red. red in Hmn. 
      intro a. rewrite Hmn. 
      reflexivity.
    Qed.

    Let e_trans: Transitive e.
    Proof.
      intros m n o Hmn Hno.
      red. red in Hmn. red in Hno.
      intro a. rewrite Hmn, Hno.
      reflexivity.
    Qed.

    Instance: Equivalence e.
    Global Instance: Setoid (F ⟶ G).

(*    Global Instance: forall (a: F ⟶ G), Setoid_Morphism (eta a).*)
  End more_arrows.

  Global Instance: CatId Object := fun _ => arrow (fun _ => cat_id ) _.
  Global Instance: CatComp Object := fun _ _ _ m n => arrow (fun a => (m a) ◎ (n a)) _.

  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv) 
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    intros.
    intros x0 x1 Hx.
    intros y0 y1 Hy.
    intros a.
    simpl.
    rewrite <- (Hx a), <- (Hy a).
    reflexivity.
  Qed.

  Let id_l' (x y: Object) (F: x ⟶ y): cat_id ◎ F = F.
  Proof.
    intro a.
    simpl.
    apply id_l.
  Qed.

  Let id_r' (x y: Object) (F: x ⟶ y): F ◎ cat_id = F.
  Proof.
    intro a.
    simpl.
    apply id_r.
  Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      intro X; simpl.
      apply comp_assoc.
    Qed.

  End comp_assoc.

  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.

End contents.

End FunCat.

Implicit Arguments Object [[Arrows0] [H] [CatId0] [CatComp0] [Arrows1] [H1] [CatId1] [CatComp1]].