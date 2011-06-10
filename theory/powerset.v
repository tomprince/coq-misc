Set Automatic Coercions Import.
Require Import
  abstract_algebra orders functors.
Require categories.setoids categories.order.


Require Import extra_tactics.

Instance: ∀ `{Equiv T}, Equiv (T → Prop) := λ _ _, ext_equiv.
Definition P (T: Type) `{Equiv T} := {f : T → Prop | Setoid_Morphism f}.
Instance: ∀ T `{Equiv T}, Le (P T) := λ T _ Q R, ∀ x, `Q x → `R x.

Instance: ∀ T `{Equiv T}, Equiv (P T) := λ _ _, sig_equiv _.
Instance: ∀ T `{Setoid T}, Setoid (P T).
Proof.
  constructor; repeat intro.
  * destruct x; apply sm_proper; auto.
  * destruct x, y; rewrite H1, <-(H0 y0); reflexivity.
  * destruct x, y, z; rewrite H2, (H0 y0), (H1 y0); reflexivity.
Qed.
Instance: ∀ T `{Setoid T}, PartialOrder (_: Le (P T)).
Proof.
  constructor.
  * typeclasses eauto.
  * repeat intro; split; repeat intro; [rewrite <-(H1 x1) | rewrite (H1 x1)]; try reflexivity;
    apply H2; [rewrite (H0 x1) | rewrite <-(H0 x1)]; try reflexivity; assumption.
  * constructor; repeat intro; repeat hyp_apply.
  * constructor; intro; [apply H0 | apply H1]; destruct x,y; simpl; [rewrite <-H2 | rewrite H2]; assumption.
Qed.

Definition PowerSet : setoids.Object → order.Object := λ x, order.object (P (setoids.T x)).
Program Instance: Fmap PowerSet := λ x y f p b, ∃ a: x, (`f a) = b ∧ p a.
Next Obligation.
  constructor; try typeclasses eauto.
  repeat intro.
  split; intros [a ?]; exists a; [ rewrite <-H | rewrite H ]; assumption.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  * constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
Typeclasses eauto := 4. (*FIXME*)
    split; intros [a ?]; exists a;
      [ rewrite <-H0, <-(H a) | rewrite H0, (H a) ]; try reflexivity; try assumption.
  * intros [??][??] ? ?.
    intros [a [??]]; exists a; auto.
Qed.
Instance: Functor PowerSet _ := {}.
Proof.
  * constructor; try typeclasses eauto.
    repeat intro.
    split; intros [z ?]; exists z; [ rewrite <-H1, <-(H0 z) | rewrite H1, (H0 z) ];
    try reflexivity; split; [rewrite <-(H z z (reflexivity _)) | | rewrite (H z z (reflexivity _)) | ]; apply H2.
  * repeat intro. simpl.
    split.
    - intros [z ?].
      destruct H1, x.
      rewrite <-(H y0 _ (reflexivity _)), <-H0, <-H1.
      assumption.
    - intro; exists x0; split;
      [reflexivity | rewrite (H x0 y0 H0); assumption ].
  * repeat intro. simpl.
    unfold compose.
    split; intros [k ?].
     - exists (`g k). rewrite <-H0. split; try apply H1.
        exists k. split; try reflexivity.
        rewrite <-(H _ _ (reflexivity k)). apply H1.
     - destruct H1 as [? [l ?]].
       exists l.
       split. rewrite H0.
       destruct H2, f. rewrite H2. assumption.
       rewrite (H _ _ (reflexivity l)). apply H2.
Qed.

Require Import dual.

Program Instance: Fmap (Arrows0:=dual.flipA) (PowerSet: _^op → _) := λ x y f p b, ∃ a: x, `f b = a ∧ p a.
Next Obligation.
  constructor; try typeclasses eauto.
  intros ???.
  destruct f.
  split; intros [a [? ?]];
    exists a;  [ rewrite <-H | rewrite H ];
    auto.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  * constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
    intros ??? ???.
    destruct f.
    split; intros [a [??]];
      exists a;
      [ rewrite <-(H a), <-H0 | rewrite (H a), H0 ];
      try reflexivity; auto.
  * intros ?? ? ? [a [??]].
    simpl.
    exists a.
    apply (H a) in H1.
    auto.
Qed.
Instance Functor_instance_1: Functor (PowerSet: _^op → _) _ := {}.
Proof.
 * intros X ??? ???.
   destruct x.
   split.
   - intros [a [??]].
     rewrite <-(H _ _ (reflexivity _)).
     rewrite <-H0, <-H1.
     assumption.
   - intro.
     exists x0.
     rewrite H0 at 2 3.
     rewrite (H _ _ (reflexivity _)).
     auto.
 * intros ??? ?? ??? ???.
   simpl. split.
   - intros [a [??]].
     exists (`g a).
     hyp_rewrite.
     intuition.
     exists a.
     intuition.
     rewrite <-(H _ _ (reflexivity _)); assumption.
   - intros [a [?[b [??]]]].
     exists b.
     unfold compose.
     destruct f, g.
     repeat hyp_rewrite.
     rewrite (H _ _ (reflexivity _)).
     intuition.
Qed.
