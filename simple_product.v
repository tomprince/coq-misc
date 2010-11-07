Require Import
    Morphisms RelationClasses Equivalence Setoid
    abstract_algebra functors categories square
    extra_tactics.

Section SimpleProduct.
Context `{Category L} `{Category R}.

Definition Object :=  prod L R.
Definition Arrow (x y: Object) := prod (fst x ⟶ fst y) (snd x ⟶ snd y).
                                  (*match x, y with
                                    (x1,x2),(y1,y2) => prod (x1 ⟶ y1) (x2 ⟶ y2)
                                  end .*)

Global Instance: Arrows Object := Arrow.
Hint Extern 4 (Arrows Object) => exact Arrow: typeclass_instances.

Section contents.
  Section e. Context {x y: Object}.
    Global Instance: Equiv (x⟶y).
    Proof. typeclasses eauto. Defined.
    Global Instance: Setoid (x⟶y).
  End e.
  Global Instance: CatId Object := fun _ => (cat_id, cat_id).
  Global Instance: CatComp Object := fun _ _ _ f g => match f, g with
                                                        | (f1,f2),(g1,g2) => (f1◎g1,f2◎g2)
                                                      end.
  Global Instance: forall x y z: Object, Proper (equiv ==> equiv ==> equiv)
    ((◎) : (y ⟶ z) -> (x ⟶ y) -> (x ⟶ z)).
  Proof.
    repeat let x := fresh in intro x; destruct x.
    split; simpl; apply comp_proper; assumption.
  Qed.

  Let id_l' (x y: Object) (f: x ⟶ y): cat_id ◎ f = f.
  Proof.
    destruct x, y, f.
    split; simpl; apply id_l.
  Qed.
  Let id_r' (x y: Object) (f: x ⟶ y): f ◎ cat_id = f.
  Proof.
    destruct x, y, f.
    split; simpl; apply id_r.
  Qed.

  Section comp_assoc.
    Context (w x y z: Object) (a: w ⟶ x) (b: x ⟶ y) (c: y ⟶ z).
    Lemma comp_assoc': c ◎ (b ◎ a) = (c ◎ b) ◎ a.
    Proof.
      destruct w, x, y, z, a, b, c.
      split; simpl; apply comp_assoc.
    Qed.
  End comp_assoc.
  Global Instance: Category Object := { comp_assoc := comp_assoc'; id_l := id_l'; id_r := id_r'}.
End contents.

End SimpleProduct.
