Set Automatic Coercions Import.
Require Import
  abstract_algebra interfaces.orders interfaces.functors.
Require categories.setoids categories.orders.
Require Import theory.setoids.

Ltac find_ext_equiv :=  match goal with [ |- @equiv _ ?e (?f ?x) (?g ?y) ] => let x:=fresh "He" in assert (He: @equiv _ (ext_equiv (H0:=e)) f g); [|apply (He _ _)] end.
Hint Extern 1 ((?f ?x) = (?g ?y)) => find_ext_equiv.
Ltac simpl_sig_equiv_hyp := repeat match goal with [ H : (@equiv _ (sig_equiv (H:=?e) ?P) ?x ?y) |- @equiv _ ?e (` _) (` _) ] => change (@equiv _ e (`x) (`y)) in H end.
Hint Extern 1 (` ?x = ` ?y) => simpl_sig_equiv_hyp.

Hint Extern 0 => unfold sig_equiv, equiv, ext_equiv.
Instance ext_Setoid: ∀ `{Setoid A} `{Setoid B}, Setoid (sig (Setoid_Morphism (A:=A) (B:=B))) := {}.
Proof. constructor; auto. Qed.

Instance ext_le: ∀ A `{Le B}, Le (A → B) := λ _ _ _ f g, ∀ x, f x ≤ g x.
Instance sig_le `{Le A} (P : A → Prop) : Le {x | P x} := λ x y, `x ≤ `y.

Require Import orders.orders.
Instance: ∀ `{Setoid A} `{PartialOrder B}, PartialOrder (sig_le Setoid_Morphism) := {}.
Proof.
  - pose (po_setoid: Setoid B); apply ext_Setoid.
  - unfold le, sig_le, le, ext_le;
    unfold equiv, sig_equiv, equiv, ext_equiv, respectful in *;
    repeat intro;
    split; intros;
    apply (po_proper _ _ (H1 _ _ (reflexivity _)) _ _ (H2 _ _ (reflexivity _))); auto.
  - unfold le, sig_le, le, ext_le.
    unfold equiv, sig_equiv, equiv, ext_equiv, respectful in *.
    constructor; auto.
    repeat intro.
    specialize H1 with x0; specialize H2 with x0.
    auto.
  - repeat intro.
    apply po_antisym.
    * transitivity (` y x0); eauto.
    * transitivity (` y x0); eauto.
Qed.

Definition power_set_equiv': ∀ `{Equiv T}, Equiv (T → Prop) := λ _ _, ext_equiv.
Hint Extern 1 (Equiv (_ → Prop)) => apply power_set_equiv' : typeclass_instances.
Instance power_set_le': ∀ T `{Equiv T}, Le (T → Prop) := λ T _ Q R, ∀ x, Q x → R x.
Hint Extern 1 (Le (_ → Prop)) => apply power_set_le' : typeclass_instances.


Definition P (T: Type) `{Equiv T} := {f : T → Prop | Setoid_Morphism f}.

Definition power_set_le: ∀ T `{Equiv T}, Le (P T) := λ _ _, sig_le _.
Hint Extern 0 (Le (P _)) => apply power_set_le : typeclass_instances.

Definition power_set_equiv: ∀ T `{Equiv T}, Equiv (P T) := λ _ _, sig_equiv _.
Hint Extern 0 (Equiv (P _)) => apply power_set_equiv : typeclass_instances.
Typeclasses Transparent P.
Instance: ∀ T `{Setoid T}, Setoid (P T) := λ _ _ _, ext_Setoid.

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
  split; intros ?; eexists;  [ rewrite <-H | rewrite H ].
  Check match H0 as H0 return match H0 return Prop with ex_intro x P' => _ x end  with ex_intro x P => P end.
  apply H0.
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
