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

Class HasNullArrows `{forall x y, NullArrow x y} :=
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

    Class Cone (c:C) (f:forall j:J, c ⟶ X j) := cone: forall (j j': J) (a:j⟶j'), (fmap X a) ◎ f j = f j'.

    Class ElimLimit: Type := limit_proj: ∀ j, limit ⟶ X j.
    Class IntroLimit: Type := make_limit: ∀ x (x_j: ∀ j, x ⟶ X j), (Cone x x_j) → (x ⟶ limit).

    Class Limit `{ElimLimit} `{IntroLimit}: Prop :=
    { limit_compat:> Cone limit limit_proj
    ; limit_factors: ∀ c ccomp ccompat, is_sole (λ h':c⟶limit, ∀ i, ccomp i = limit_proj i ◎ h') (make_limit c ccomp ccompat) }.

    Lemma limit_round_trip `{Limit} (x: C) (h: ∀ j, x ⟶ X j) compat j:
      limit_proj j ◎ make_limit x h compat = h j.
    Proof. symmetry. apply limit_factors. Qed.
  End def.

  Lemma limits_unique `{Limit c} `{Limit c'}:
    iso_arrows
      (make_limit c c' (limit_proj c') _)
      (make_limit c' c (limit_proj c) _).
  Proof with intuition.
    unfold iso_arrows.
    revert c H3 H4 H5 c' H6 H7 H8.
    cut (∀ `{Limit x} `{Limit y}, make_limit x y (limit_proj y) _ ◎ make_limit y x (limit_proj x) _ = cat_id)...
    pose proof proj2 (limit_factors x x (limit_proj x) _) as Q.
    rewrite (Q cat_id)...
    + rewrite Q...
      rewrite comp_assoc.
      repeat rewrite limit_round_trip...
    + rewrite right_identity...
  Qed.
End Limits.

