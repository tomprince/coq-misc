Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import interfaces.abstract_algebra interfaces.functors theory.categories.
(* me *)
Require Import square.

Set Automatic Introduction.

Section Retract.

Context `{Category C}.

Class Retract {a b a' b': C} (i: a'⟶a) (p: a⟶a') (i':b'⟶b) (p':b⟶b') (f: a⟶b) (g: a'⟶b') := retract {
  top : p ◎ i = cat_id;
  bottom : p' ◎ i' = cat_id;
  sq_l : Square g f i i';
  sq_r : Square f g p p'
}.

Section stuff_1.
Context (a b:C) (i:a ⟶ b) (p: b⟶a) (HH:p ◎ i = cat_id).
Program Instance: Retract i p cat_id cat_id p cat_id .
Next Obligation. apply id_l. Qed.
Next Obligation. unfold Square; rewrite HH; apply id_l. Qed. 
Next Obligation. red; reflexivity. Qed.

Program Instance: Retract cat_id cat_id i p i cat_id.
Next Obligation. apply id_l. Qed.
Next Obligation. red; reflexivity. Qed.
Next Obligation. red. rewrite HH; symmetry; apply id_l. Qed.

Context (c d:C) (j:c ⟶ d) (q: d⟶c) (II:q ◎ j = cat_id).
Context (f:a⟶c).
Program Instance: Retract i p j q (j ◎ f ◎ p) f.
Next Obligation. red. rewrite <- comp_assoc, HH, id_r; reflexivity. Qed.
Next Obligation. red. rewrite comp_assoc, comp_assoc, II, id_l; reflexivity. Qed.
End stuff_1.

Section stuff_2.
Context (a b:C) (i:a ⟶ b) (p: b⟶a) (HH:p ◎ i = cat_id).
Context (c:C) (j:c ⟶ b) (q: b⟶c) (II:q ◎ j = cat_id).
Program Instance: Retract i p j q cat_id (q ◎ i).
Next Obligation. red. rewrite id_l, comp_assoc. admit. Qed. 
Next Obligation. red. rewrite id_r. admit. Qed.
End stuff_2.

Section stuff_3.
Context (a b x y c:C) (i:a ⟶ b) (p: x⟶y) (f:a⟶x) (g:b⟶y).
Context (Sq: Square i p f g).
Context (h:b⟶x) (UT:h◎i = f) (LT:p◎h = g).
Context (j:b⟶c) (q:c⟶x) (F:q◎j=h).
Context (q':x⟶c) (L:q◎q'=cat_id) (LL:q'◎f = j◎i).
(*Context (j':c⟶b) (L:j◎j'=cat_id) (LL:q'◎f = j◎i).*)
Program Instance: Retract cat_id cat_id q' q (j◎i) f. 
Next Obligation. apply id_l. Qed.
Next Obligation. red. rewrite id_r. apply LL. Qed.
Next Obligation. red. rewrite id_r, comp_assoc. rewrite F. apply UT. Qed.

End stuff_3.

End Retract.
