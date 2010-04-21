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

Let F (a:A) : Object J A := functor_category.object (fun _:J=>a) _ _.

Global Instance F': Fmap F := fun (a a':A) (f:a ⟶ a') => functor_category.arrow (F a) (F a')
  (fun (j:J) => f) constant_transformation.

Existing Instance functor_category.Category_instance_0.

Global Instance: Functor F F'.
Proof.
constructor; try apply _.
intros a b; constructor; try apply _;
 intros f g Hfg; intros j; simpl; exact Hfg.
intros a j; simpl; reflexivity.
intros; intro j; simpl; reflexivity.
Qed.

End yonedad.

Require categories.setoid.
Require comma.

Section lim.
Context `{Category J}.
Context `{!Functor (X:J->setoid.Object) X'}.
Existing Instance Arrows0.


Let Slice := comma.Object (*L:=setoid.Object) (R:=unit) (C:=functor_category.Object J setoid.Object*) (l := fun x:setoid.Object => functor_category.object (F x) _ _) (r := fun _:unit => functor_category.object X X' Functor0).


(*Context  (j k: J) (f:j⟶k).
Check proj1_sig (fmap X f).*)

Let x_t := {u :forall j:J, X j | forall (j k: J) (f:j⟶k), proj1_sig (fmap X f) (u j) =  u k}.
Global Instance e : Equiv x_t := fun u v => forall j:J, proj1_sig u j = proj1_sig v j.
Let e_refl : Reflexive e.
Proof. intros x j; reflexivity. Qed.
Let e_sym: Symmetric e.
Proof. intros x y Hxy j; symmetry; apply Hxy. Qed.
Let e_trans: Transitive e.
Proof. intros x y z Hxy Hyz j; rewrite (Hxy j), (Hyz j); reflexivity. Qed.
Instance: Equivalence e.
Global Instance: Setoid x_t.
Let x := setoid.object x_t e _.

Instance: NaturalTransformation (fun j:J => x ⟶ X j).
Let Ix := 

Let II : initial (H:=comma.e) (X:=Slice) x.
Proof.
  intro y. 




