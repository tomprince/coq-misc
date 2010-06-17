Require Import
   Morphisms RelationClasses Equivalence Setoid
   abstract_algebra square.
Require comma.
(* me *)
Require Import retract.
Require comma.

Set Implicit Arguments.
Section test.
Context `{Category M}.
Class ArrowClass : Type := arrowClass : forall {x y: M}, (x ⟶ y) -> Prop.
Class MorphismClass (P: ArrowClass) := 
  Prespect: forall (x y: M) (f g: x ⟶ y), f = g -> (P _ _ f <-> P _ _ g).

Instance AndArrowClass (P Q: ArrowClass) : ArrowClass := fun {x y: M} (f: x ⟶ y) => P _ _ f /\ Q _ _ f.

Class Lift (L R: ArrowClass) : Type := lift : forall (a b x y:M) (i:a⟶b) (p:x⟶y) `{!Square i p f g} `(L _ _ i) `(R _ _ p), b ⟶ x.

Class Factorization {x y: M} (f: x ⟶ y) := {
  z : M;
  l : x⟶z;
  r : z⟶y;
  comm : r◎l = f
}.

End test.
Implicit Arguments ArrowClass [[Arrows0]].
Implicit Arguments l [[M] [Arrows0] [H] [CatComp0] [x] [y] [Factorization]].
Implicit Arguments r [[M] [Arrows0] [H] [CatComp0] [x] [y] [Factorization]].
Implicit Arguments z [[M] [Arrows0] [H] [CatComp0] [x] [y] [Factorization]].
Implicit Arguments lift [[M] [Arrows0] [H] [CatComp0] [Lift] [a] [b] [x] [y]].
Notation "P & Q" := (AndArrowClass P Q).
Notation "f '//' L" := (L _ _ f) (at level 60).

Section WeakFactorizationSystem.
Context `{Category C}.
Context {L R: ArrowClass C}.
Context {lift : Lift L R}.
Context `{fact : forall `{f:x⟶y}, Factorization f}.
Class WeakFactorizationSystem : Prop := {
  left_factor_proper : forall x y (f g: x⟶y), f = g -> ((f // L) <-> (f // L));
  right_factor_proper : forall x y (f g: x⟶y), f = g -> (f // R <-> f // R);
  factor_classes: forall (x y: C) (f: x ⟶ y), (l f) // L /\ (r f) // R;
  lift_commute: forall (a b x y:C) (i:a⟶b) (p:x⟶y) f g (Sq : Square i p f g) (Li: L i) (Rp: R p)  , let h := (lift Sq Li Rp) in h◎i=f /\ g = p◎h;
  left_retract: forall x y x' y' `(l:x⟶y) (l':x'⟶y') `(!Retract i i' p p' l' l), L l' -> L l;
  right_retract: forall x y x' y' `(r:x⟶y) (r':x'⟶y') `(!Retract i i' p p' r' r), R r' -> R r 
}.

Section Lemmas.
Context `{WeakFactorizationSystem}.

Lemma lem `(i:a⟶b) (Hyp:forall `(p:x⟶y) `(!Square i p f g), R p -> {h | (h◎i = f /\ p◎h = g)}): L i.
Proof.
assert (R (r i)). apply factor_classes.
assert (sq : Square i (r i) (l i) cat_id).
  red; rewrite id_l; rewrite comm; reflexivity.
pose (h:=Hyp _  _ _ _ _ sq H2).
destruct h. destruct a0.
eapply left_retract.
split.
- apply id_l.
- apply H4.
- apply (@square _ _ _ _ _ _ _ _ i (l i) cat_id ).
  red. rewrite id_r. apply H3.
- apply (@square _ _ _ _ _ _ _ _ (l i) i cat_id (r i)).
  red. rewrite id_r. rewrite comm. reflexivity.
- apply factor_classes.
Qed.
End Lemmas.

End WeakFactorizationSystem.
Implicit Arguments WeakFactorizationSystem [[Arrows0] [H] [CatId0] [CatComp0] [lift]].

Section WeakModCat.
Context `(Category M).
Context (W C F : ArrowClass M).
Context `{!WeakFactorizationSystem M (C&W) F (lift:=Llift) Lfact}.
Context `{!WeakFactorizationSystem M C (F&W) (lift:=Rlift) Rfact}.
Implicit Arguments W [x y].
Class WeakModelCategory : Prop  := {
  cat :> Category M;
  Wrespect:> MorphismClass W;
  Crespect: MorphismClass C;
  Frespect: MorphismClass F;
  Lfactor: WeakFactorizationSystem M (C&W) F Lfact;
  Rfactor: WeakFactorizationSystem M C (F&W) Rfact;
  W2of3: forall x y z (f:x ⟶ y) (g:y ⟶ z), (W f /\ W g -> W (g◎f)) /\ (W f /\ W (g◎f) -> W g) /\ (W g /\ W (g◎f) -> W f)
}.

End WeakModCat.

Section WeakModCat2.
Context `(Category M).
Context (TC TF C F : ArrowClass M).
Context `{!WeakFactorizationSystem M (H:=H) (CatComp0:=CatComp0) TC F (lift:=Llift) Lfact}.
Context `{!WeakFactorizationSystem M (H:=H) (CatComp0:=CatComp0) C TF (lift:=Rlift) Rfact}.
Class WeakModelCategory2 : Prop  := {
  cat2 :> Category M;
  TCrespect:> MorphismClass TC;
  TFrespect:> MorphismClass TF;
  Crespect2: MorphismClass C;
  Frespect2: MorphismClass F;
  TCisC: forall `(f:x⟶y), TC f -> C f;
  TFisF: forall `(f:x⟶y), TF f -> F f;
  Lfactor2: WeakFactorizationSystem M TC F Lfact;
  Rfactor2: WeakFactorizationSystem M C TF Rfact
}.
Check  W2of3: forall x y z (f:x⟶y) (g:y ⟶ z), (W f /\ W g -> W (g◎f)) /\ (W f /\ W (g◎f) -> W g) /\ (W g /\ W (g◎f) -> W f).
}.
