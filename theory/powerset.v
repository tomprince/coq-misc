Set Automatic Coercions Import.
Require Import
  abstract_algebra interfaces.orders interfaces.functors.
Require categories.setoids categories.orders.
Require Import theory.setoids.
Require Import orders.orders.

Ltac find_ext_equiv :=  match goal with [ |- @equiv _ ?e (?f ?x) (?g ?y) ] => let x:=fresh "He" in assert (He: @equiv _ (ext_equiv (H0:=e)) f g); [|apply (He _ _)] end.
Hint Extern 1 ((?f ?x) = (?g ?y)) => find_ext_equiv.
Hint Extern 1 ((?f ?x) = (?g ?y)) => find_ext_equiv: typeclass_instances.
Ltac simpl_sig_equiv_hyp := repeat match goal with [ H : (@equiv _ (sig_equiv (H:=?e) ?P) ?x ?y) |- @equiv _ ?e (` _) (` _) ] => change (@equiv _ e (`x) (`y)) in H end.
Hint Extern 1 (` ?x = ` ?y) => simpl_sig_equiv_hyp.
Hint Extern 1 (` ?x = ` ?y) => simpl_sig_equiv_hyp: typeclass_instances.

Local Hint Extern 0 => unfold sig_equiv, equiv, ext_equiv.
Instance ext_Setoid `{Setoid A} `{Setoid B}: Setoid (sig (Setoid_Morphism (A:=A) (B:=B))) := _.
Proof. constructor; auto. Qed.

Instance ext_le A B `{Le B}: Le (A → B) := pointwise_relation A (≤).
Require Import order.induced.
Instance sig_le `{Le A} (P : A → Prop) : Le {x | P x} := induced_le _ _ (@proj1_sig _ _).

Instance: ∀ `{Setoid A} `{PartialOrder B}, PartialOrder (sig_le Setoid_Morphism) := {}.
Proof.
  - pose (po_setoid: Setoid B); apply ext_Setoid.
  Typeclasses Transparent ext_le.
  - unfold le, sig_le, le, induced_le, ext_le, pointwise_relation;
    unfold equiv, sig_equiv, equiv, ext_equiv, respectful in *.
    pose (po_setoid: Setoid B);
    repeat intro.
    split; intros;
    intro;
    now apply (po_proper _ _ (H1 _ _ (reflexivity _)) _ _ (H2 _ _ (reflexivity _))).
  - unfold le, sig_le, induced_le, le, ext_le, pointwise_relation.
    unfold equiv, sig_equiv, equiv, ext_equiv, respectful in *.
    constructor; auto.
    repeat intro.
    specialize H1 with a; specialize H2 with a.
    auto.
  - repeat intro.
    apply po_antisym.
    * transitivity (` y x0); eauto.
    * transitivity (` y x0); eauto.
Qed.

Definition power_set_equiv' `{Equiv T}: Equiv (T → Prop) := ext_equiv.
Hint Extern 1 (Equiv (_ → Prop)) => apply power_set_equiv' : typeclass_instances.
Instance power_set_le' `{Equiv T}: Le (T → Prop) := λ Q R, ∀ x, Q x → R x.
Hint Extern 1 (Le (_ → Prop)) => apply power_set_le' : typeclass_instances.

Instance power_set_joint' `{Equiv T}: Meet (T → Prop) := λ p q, λ t, p t ∧ q t.
Instance power_set_meet' `{Equiv T}: Meet (T → Prop) := λ p q, λ t, p t ∨ q t.
Instance power_set_top' T: Top (T → Prop) := λ t:T, True.
Instance power_set_bottom' T: Top (T → Prop) := λ t:T, False.

Definition P (T: Type) `{Equiv T} := {f : T → Prop | Setoid_Morphism f}.

Definition power_set_le: ∀ T `{Equiv T}, Le (P T) := λ _ _, sig_le _.
Hint Extern 0 (Le (P _)) => apply power_set_le : typeclass_instances.

Definition power_set_equiv: ∀ T `{Equiv T}, Equiv (P T) := λ _ _, sig_equiv _.
Hint Extern 0 (Equiv (P _)) => apply power_set_equiv : typeclass_instances.
Typeclasses Transparent P.
Instance: ∀ T `{Setoid T}, Setoid (P T) := λ _ _ _, ext_Setoid.

Program Instance power_set_meet `{Setoid T}: Meet (P T) := λ p q, λ t, p t ∧ q t.
Next Obligation.
  constructor; try typeclasses eauto.
  repeat intro.
  rewrite !(sm_proper _ _ H0). firstorder.
Qed.
Program Instance power_set_join `{Setoid T}: Meet (P T) := λ p q, λ t, p t ∨ q t.
Next Obligation.
  constructor; try typeclasses eauto.
  repeat intro.
  rewrite !(sm_proper _ _ H0). firstorder.
Qed.
Program Instance power_set_top `{Setoid T}: Top (P T) := λ t:T, True.
Next Obligation.
  constructor; try typeclasses eauto.
  hnf; reflexivity.
Qed.
Program Instance power_set_bottom `{Setoid T}: Top (P T) := λ t:T, False.
Next Obligation.
  constructor; try typeclasses eauto.
  hnf; reflexivity.
Qed.

Instance: ∀ T `{Setoid T}, PartialOrder (_: Le (P T)).
Proof.
  intros.
  eapply (@PartialOrder_instance_0 T Ae H Prop Equiv_instance_0 impl ).
Hint Unfold iff equiv le Equiv_instance_0.
  constructor; typeclasses eauto || auto 6.
Qed.

Definition PowerSet : setoids.Object → orders.Object := λ x, orders.object (P (setoids.T x)).
Program Instance: Fmap PowerSet := λ x y f p b, ∃ a: x, (`f a) = b ∧ p a.
Next Obligation.
  constructor; try typeclasses eauto.
  repeat intro.
  split; intros [a Ha]; exists a;  [ rewrite <-H | rewrite H ]; apply Ha.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  - constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
    repeat intro.
    split; intros [a Ha]; exists a; [symmetry in H | symmetry in H0];
    rewrite (H a a (reflexivity _)); firstorder.
  - intros. intros ? [a Ha].
    exists a.
    firstorder.
Qed.

(*
Definition t A (P: A → Prop) (x : ex P) : match x return Prop with ex_intro x' P' => P x' end
:=  match x with ex_intro x' P' => P' end.
destruct x.
intro.
Proof  λ x, match x with ex_intro x' P' => P'.
 Check proj2_sig H0. assumption.
Qed.
Next Obligation.
  constructor; try typeclasses eauto.
  * constructor; try typeclasses eauto.
    constructor; try typeclasses eauto.
    split; intros [a ?]; exists a;
      [ rewrite <-H0, <-(H a) | rewrite H0, (H a) ]; try reflexivity; try assumption.
  * intros [??][??] ? ?.
    intros [a [??]]; exists a; auto.
Qed.
*)
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
      unfold id.
      rewrite <-(H y0 _ (reflexivity _)). simpl. rewrite <-H0, <-H1.
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

Program Instance: Fmap (Arrows0:=dual.flipA) PowerSet := λ x y f p b, ∃ a: x, `f b = a ∧ p a.
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

Instance Functor_instance_1: Functor PowerSet _ := {}.
Proof.
 * intros X ??? ???.
   destruct x.
   split.
   - intros [a [??]].
     rewrite <-(H _ _ (reflexivity _)).
     simpl.
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
     rewrite H1.
     intuition.
     exists a.
     intuition.
     rewrite <-(H _ _ (reflexivity _)); assumption.
   - intros [a [?[b [??]]]].
     exists b.
     unfold compose.
     destruct f, g.
     rewrite H2, H1.
     rewrite (H _ _ (reflexivity _)).
     intuition.
Qed.
