Require Import Morphisms.
Require Import RelationClasses.
Require Import Equivalence.
Require Import Setoid.

(* Eelis *)
Require Import categories abstract_algebra functors.
(* me *)
Require Import constant_functor unit_category.
Require functor_category.

Set Automatic Introduction.

Section yonedad.
Context `{Category A} `{Category J}.

Import functor_category.
(*Let Object := functor_category.Object J A.*)
(*Let Arrow (F G : Object) := functor_category.Arrow F G.*)

Definition F (a:A) : Object J A := functor_category.object (fun _:J=>a) _ _.

Global Instance F': Fmap F := fun (a a':A) (f:a ⟶ a') => functor_category.arrow (F a) (F a')
  (fun (j:J) => f) constant_transformation.

Existing Instance functor_category.Category_instance_0.

Global Instance: Functor F F'.
Proof. do 4 stuff; [stuff | stuff| do 4 stuff| do 3 stuff ]. Qed.

End yonedad.

Require categories.setoid.
Require comma.

Section lim.
Context `{Category J}.
Context `{!Functor (X:J->setoid.Object) X'}.

Let l := fun x:setoid.Object => functor_category.object (F x) _ _.
Let r := fun _:unit => functor_category.object X X' Functor0.

Let Slice := comma.Object (l:=l) (r:=r).

Require Import theory.setoids.
Let x_t := {u :forall j:J, X j | forall (j k: J) (f:j⟶k), proj1_sig (fmap X f) (u j) =  u k}.
Let sss : Setoid x_t := sig_Setoid _.
Existing Instance sss.

Let x := setoid.object x_t _ sss.

Ltac apply_head := repeat intro; match goal with [ H:_ |- _] => idtac H; apply H end.
 Ltac stuff := simpl || apply_head || intuition || trivial || constructor || reflexivity || id_rewrite || comp_rewrite || hyp_rewrite || intro.

Let Fx := fun j:J, x.
Let etaj (j:J) (a:x) : X j := proj1_sig a j.
Section etaj.
Context (j:J).
Global Instance: Setoid_Morphism (etaj j).
Proof. repeat stuff. Qed.
End etaj.

Let eta : Fx ⇛ X :=  (fun j:J => exist Setoid_Morphism (etaj j) _).
Global Instance: NaturalTransformation eta.
Proof.
intros j j' f; intros m n Hmn.
simpl. unfold Basics.compose.
unfold etaj.
rewrite (proj2_sig n j j').
intuition.
Qed.

Let Feta := (functor_category.arrow (F x) (functor_category.object X X' _) eta _).
Let co := comma.object (r:= fun _ => functor_category.object X _ _) x tt  Feta.

Section initarrow.
Context (y:Slice).
Let xinx_t (a: comma.Lobj y) (j:J) : X j := proj1_sig (comma.Cmap y j) a.

Lemma inx_t (a: comma.Lobj y) (j k: J) (f:j⟶k) : (` (fmap X f)) (xinx_t a j) = (xinx_t a k).
Proof.
  unfold xinx_t.
  set (Cmap := (comma.Cmap y)).
  set (Robj := r (comma.Robj y)).
  set (Lobj := l (comma.Lobj y)).
  assert (eq (fmap X f) (fmap Robj f)) by reflexivity; hyp_rewrite.
  change (` (fmap Robj f ◎ Cmap j) a = ` (Cmap k) a).
  transitivity (` (Cmap k ◎ fmap Lobj f) a).
    symmetry; apply (natural (η:=functor_category.eta _ _ (comma.Cmap y)) _ _ _ a); auto.
    stuff; stuff. reflexivity.
Qed.

Definition aa (a : comma.Lobj y) : x_t := exist _ _ (inx_t a).
Global Instance: Setoid_Morphism (Beq:= sig_equiv _) aa.
Proof.
  stuff. stuff.
  constructor; apply _.
  apply _.
  intros b b' Hb j. simpl.
  unfold xinx_t.
  pose (proj2_sig (comma.Cmap y j)); rewrite Hb.
  reflexivity.
Qed.

Program Let aaE : l (comma.Lobj y) ⇛ Fx :=  (fun j:J => exist Setoid_Morphism aa _).
Global Instance: NaturalTransformation aaE.
Proof.
  intros s t f g g' Hg j; simpl.
  unfold xinx_t.
  pose (proj2_sig (comma.Cmap y j)); rewrite Hg.
  reflexivity.
Qed.

End initarrow.


Require dual.



Let II : initial (Arrows0:=dual.flipA) co.
Proof.
  intro y.
