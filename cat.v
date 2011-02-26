Require Import
   Morphisms RelationClasses Equivalence Setoid Program
   abstract_algebra categories interfaces.functors.
Require Import rings.
Require dual.

(* me *)

Require Import extra_tactics.

Ungereralizable Arguments Initial [X Arrows0 H].
Ungereralizable Arguments InitialArrow [X Arrows0 H].
Section terminality.
  Context `{Category X}.

  Class TerminalArrow (x: X): Type := terminal_arrow: ∀ y, y ⟶ x.

  Class Terminal (x: X) `{TerminalArrow x}: Prop := terminal_arrow_unique: ∀ y f', terminal_arrow y = f'.

  Definition terminal (x: X): Type := ∀ y: X, sig (λ a: y ⟶ x, ∀ a': y ⟶ x, a = a').

  Section dual.
    Context `{Terminal x}.
    Global Instance: InitialArrow (Arrows0 := dual.flipA) x := terminal_arrow.
    Global Instance: Initial (Arrows0 := dual.flipA) x := terminal_arrow_unique.
  End dual.
  Definition terminals_unique' (x x': X) `{Terminal x} `{Terminal x'}:
    iso_arrows (terminal_arrow x': x' ⟶ x) (terminal_arrow x) :=
    (initials_unique' (H0:=dual.cat (c:=H0)) x' x).
End terminality.
Ungereralizable Arguments Terminal [X Arrows0 H].
Ungereralizable Arguments TerminalArrow [X Arrows0 H].

Section Null.
Context `{Category C}.
Context `{InitialArrow C z}.
Context `{TerminalArrow C z}.
Class Null : Prop :=
{ null_initial :> Initial z;
  null_terminal :> Terminal z}.
End Null.
Ungereralizable Arguments Null [Arrows H].
Section NullArrow.
Context `{Category C}.
Class NullArrow x y := null_arrow: x ⟶ y.

Class HasNullArrows `{∀ x y, NullArrow x y} :=
{ left_null : ∀ x y z (f:x⟶y), (null_arrow: y⟶z) ◎ f = null_arrow
; right_null : ∀ x y z (f:y⟶z), f ◎ (null_arrow: x⟶y) = null_arrow }.
Context `{Null C (Arrows0:=Arrows0) H z}.
Section x.
Context (x y: C).
Global Instance: NullArrow x y := initial_arrow y ◎ terminal_arrow x.
End x.
Global Instance: HasNullArrows.
Proof.
  constructor;
  unfold null_arrow, NullArrow_instance_0;
  intros r s t f;
  [ rewrite <- comp_assoc, (terminal_arrow_unique r) | rewrite comp_assoc, (initial_arrow_unique t) ];
  reflexivity.
Qed.
End NullArrow.

Section Limits.
  Context `{Category C, Category J}.
  Context `{!Functor (X:J→C) X'}.

  Section def.

    Context (limit: C).

    Class Cone (c:C) (f:∀ j:J, c ⟶ X j) := cone: ∀ (j j': J) (a:j⟶j'), (fmap X a) ◎ f j = f j'.

    Class ElimLimit: Type := limit_proj: ∀ j, limit ⟶ X j.
    Class IntroLimit: Type := make_limit: ∀ x (x_j: ∀ j, x ⟶ X j), (Cone x x_j) → (x ⟶ limit).

    Class Limit `{ElimLimit} `{IntroLimit}: Prop :=
    { limit_compat:> Cone limit limit_proj
    ; limit_factors: ∀ c ccomp ccompat, is_sole (λ h':c⟶limit, ∀ i, limit_proj i ◎ h' = ccomp i) (make_limit c ccomp ccompat) }.

    Lemma limit_round_trip `{Limit} (x: C) (h: ∀ j, x ⟶ X j) compat j:
      limit_proj j ◎ make_limit x h compat = h j.
    Proof. apply limit_factors. Qed.
  End def.

  Lemma limits_unique `{Limit c} `{Limit c'}:
    iso_arrows
      (make_limit c c' (limit_proj c') _)
      (make_limit c' c (limit_proj c) _).
  Proof with intuition.
    revert dependent c'; revert dependent c.
    unfold iso_arrows.
    cut (∀ `{Limit x} `{Limit y}, make_limit x y (limit_proj y) _ ◎ make_limit y x (limit_proj x) _ = cat_id)...
    pose proof proj2 (limit_factors x x (limit_proj x) _) as Q.
    setoid_rewrite Q...
    + rewrite comp_assoc.
      repeat rewrite limit_round_trip...
    + rewrite right_identity...
  Qed.
End Limits.

Section Equalizer.
  Context `{Category C} {J: Type}.
  Context {x y: C} (f: ∀ j:J, x⟶y).

  Section def.
    Context (equalizer: C).

    Class EqualizerCone c (p: c⟶x): Prop := equalizer_cone: ∀ j j', f j ◎ p = f j' ◎ p.

    Class ElimEqualizer: Type := equalizer_proj: equalizer ⟶ x.
    Class IntroEqualizer: Type := make_equalizer: `(EqualizerCone c p → (c ⟶ equalizer)).

    Class Equalizer `{ElimEqualizer} `{IntroEqualizer}: Prop :=
    { equalizer_compat:> EqualizerCone equalizer equalizer_proj
    ; equalizer_factors: ∀ c p cp_cone, is_sole (λ h:c⟶equalizer, equalizer_proj ◎ h = p) (make_equalizer c p cp_cone) }.

    Lemma equalizer_round_trip `{Equalizer} (c: C) (p: c ⟶ x) cp_cone:
      equalizer_proj ◎ make_equalizer c p cp_cone = p.
    Proof. apply equalizer_factors. Qed.
  End def.

  Lemma equalizers_unique `{Equalizer c} `{Equalizer c'}:
    iso_arrows
      (make_equalizer c c' (equalizer_proj c') _)
      (make_equalizer c' c (equalizer_proj c) _).
  Proof with intuition.
    revert dependent c'; revert dependent c.
    unfold iso_arrows.
    cut (∀ `{Equalizer c} `{Equalizer c'}, make_equalizer c c' (equalizer_proj c') _ ◎ make_equalizer c' c (equalizer_proj c) _ = cat_id)...
    pose proof proj2 (equalizer_factors c c (equalizer_proj c) _) as Q.
    setoid_rewrite Q...
    + rewrite comp_assoc.
      repeat rewrite equalizer_round_trip...
    + rewrite right_identity...
  Qed.
End Equalizer.
Section equalizer_as_limit.
  Context `{Category C}.
  Ungereralizable Arguments Equalizer [C Arrows0 H CatComp0].
  Context `{Equalizer _ (H:=_) J x y f c}.
  Inductive I := X | Y.
  Instance: Arrows I := fun a b => match a, b with
                                     | X, X | Y, Y => unit
                                     | X, Y => J
                                     | Y, X=> Empty_set
                                   end.
  Let F (a: I) := match a with  X => x | Y => y end.
  Instance: Fmap F := fun a b => match a, b with
                                   | X, X | Y, Y => fun _ => cat_id
                                   | X, Y => fun j => f j
                                   | Y, X => fun j => match j with end
                                 end.

  Context (j:J).
  Instance: ElimLimit (J:=I) (X:=F) c := fun i => match i with X => equalizer_proj c | Y => f j ◎ equalizer_proj c end.
  Instance: ∀ (d : C) (d_j : ∀ j : I, d ⟶ F j),
       Cone d d_j → EqualizerCone f d (d_j X).
  Proof. intros * cone ??; transitivity (d_j Y); [ | symmetry]; apply (cone X Y). Qed.
  Instance: IntroLimit (J:=I) (X:=F) c := fun d d_j d_cone => make_equalizer f c d (d_j X) _.
  Instance: Cone (J:=I) c (limit_proj c).
  intros [][]a.
  + apply left_identity.
  + apply (equalizer_compat _ _ a).
  + destruct a.
  + apply left_identity.
  Qed.
  Instance: Limit (J:=I) c.
  constructor.
  typeclasses eauto.
  intros *.
  pose (equalizer_factors f c c0 (ccomp X) _).
  split.
  + intros [].
    - apply i.
    - rewrite <- (ccompat X Y j).
      unfold limit_proj, ElimLimit_instance_0.
      simpl.
      setoid_rewrite <- comp_assoc.
      unfold make_limit, IntroLimit_instance_0.
      rewrite equalizer_round_trip; try typeclasses eauto.
      reflexivity.
  + intros ? H4.
    apply i.
    apply (H4 X).
  Qed.
End equalizer_as_limit.
Ungereralizable Arguments HasNullArrows [C Arrows0 H CatComp0].
Section Kernel.
  Context `{Category C, HasNullArrows (H:=_) C}.
  Context `(f: x⟶y).

  Section def.
    Context (kernel: C).
    Class ElimKernel: Type := kernel_inj: kernel⟶x.
    Class IntroKernel: Type := make_kernel: ∀ z (i: z⟶x) (_:f◎i = null_arrow), z⟶kernel.
    Class Kernel `{ElimKernel} `{IntroKernel}: Prop :=
    { kernel_compat: f◎kernel_inj = null_arrow
    ; kernel_factors: ∀ z i Ki, is_sole (λ i':z⟶kernel, kernel_inj◎i'=i) (make_kernel z i Ki) }.

    Lemma kernel_round_trip `{Kernel} z i compat: kernel_inj ◎ make_kernel z i compat = i.
    Proof. apply kernel_factors. Qed.
  End def.

  Lemma kernels_unique `{Kernel k} `{Kernel k'}:
     iso_arrows
       (make_kernel k k' (kernel_inj k') (kernel_compat _))
       (make_kernel k' k (kernel_inj k) (kernel_compat _)).
  Proof with intuition.
    revert dependent k'; revert dependent k.
    unfold iso_arrows.
    cut (∀ `{Kernel k} `{Kernel k'}, make_kernel k k' (kernel_inj k') (kernel_compat _) ◎ make_kernel k' k (kernel_inj k) (kernel_compat _) = cat_id)...
    pose proof proj2 (kernel_factors k k (kernel_inj k) (kernel_compat _)) as Q.
    setoid_rewrite Q...
    + rewrite comp_assoc.
      repeat rewrite kernel_round_trip...
    + rewrite right_identity...
  Qed.
End Kernel.


Require categories.setoid.

Section SetoidLimits.
Context `{Category J} X `{!Functor (X:J->setoid.Object) X_fmap}.

Let product := ∀ j, setoid.T (X j).
Let sub := λ (x: product), ∀ j j' (f: j⟶j'), ` (fmap X f) (x j) = (x j').
Definition limit := sig sub.
Instance e: Equiv limit := λ x y: limit, ∀ j, `x j = `y j.
Instance: Setoid limit.
Proof. prove_equivalence. Qed.
Definition l := setoid.object limit _ _.

Section elim.
Context (j:J).
Definition elim : limit → setoid.T (X j) := λ x, `x j.
Global Instance: Proper ((=)==>(=)) elim.
Proof. hnf; unfold elim; auto. Qed.
Global Instance: Setoid_Morphism (elim).
End elim.
Program Instance: ElimLimit (X:=X) l := elim.

Instance: Cone (X:=X) l (limit_proj _).
hnf. intros.
intros [][]?. simpl. unfold elim, compose. simpl in *.
unfold sub in s.
rewrite s. apply H1.
Qed.

Section intro.
Context (x: setoid.Object) (x_j : ∀ j : J, x ⟶ X j) `(cone:!Cone x x_j).
Program Definition intro : setoid.T x → limit := λ a j, ` (x_j j) a.
Next Obligation.
intros j j' f; apply (cone j j' f a a); reflexivity.
Qed.
Let kk {A B}: forall (f: setoid.Arrows_instance_0 A B), Setoid_Morphism (`f) := @proj2_sig _ _.
Coercion kk: setoid.Arrows_instance_0 >-> Setoid_Morphism.
Instance: Proper ((=)==>(=)) intro.
intros ??? j. simpl.
apply sm_proper.
auto.
Qed.
Global Instance: Setoid_Morphism intro.
End intro.
Program Instance: IntroLimit (X:=X) l := intro.

Global Program Instance: Limit l.
Next Obligation.
  split.
  + intros ????.
    simpl; unfold elim, intro, compose; simpl.
    destruct (ccomp i).
    apply sm_proper.
    auto.
  + intros L compat x y Hxy j.
    apply (compat j x y).
    assumption.
Qed.

End SetoidLimits.
