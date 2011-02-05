Require Import
   Morphisms RelationClasses Equivalence Setoid Program
   abstract_algebra categories.
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
Context `{Null C (Arrows0:=Arrows0) H z}.
Set Typeclasses Debug.
Context (x y: C).
Check initial_arrow (Arrows0:=Arrows0) y ◎ terminal_arrow (Arrows0:=Arrows0) x.
Class NullArrow (x y: C) (f: x⟶y) : Prop := null_arrow: f = initial_arrow y ◎ terminal_arrow x.
End NullArrow.

Require Import interfaces.functors.
Section Limits.
  Context `{Category C, Category J}.
  Context `{!Functor (X:J→C) X'}.
Require cone.

Context `{x : C}.
Context `{x_j : ∀ j: J, x ⟶ X j}.
Context `{ mor : ∀ (c:C) (c_j: ∀ j, c⟶X j) `{!cone.Cone c c_j}, c ⟶ x }.
Class Limit : Prop :=
{ limit_cone :> cone.Cone x x_j
; limit_mor :> ∀ (c:C) `(c_cone: !cone.Cone c c_j), cone.ConeMorphism _ limit_cone (mor c c_j _)
; limit_terminal :> Terminal _ (H1:=fun c: cone.Object => cone.arrow c (cone.object x x_j limit_cone) (mor _ _ _) (limit_mor _ _ )) }.

End Limits.

Require Import categories.empty.
Section test.
Context `{Category C}.
Context `{Limit C (J:=Empty_set) (Arrows1:=_) (CatComp0:=_) (H:=_) (Arrows0:=_) (X:=Empty_map) (x:=x) (X':=Empty_map) (x_j:=Empty_map)}.

Let CC (y: C) : cone.Object (X:=Empty_map:Empty_set→C) (X':=Empty_map) :=  (cone.object y Empty_map Empty_map).
Let CCM {y: C} (f: y⟶x) : (CC y) ⟶ (cone.object _ _ limit_cone) :=  (cone.arrow (CC y) (cone.object _ _ limit_cone) f Empty_map).
Global Instance: TerminalArrow x := fun y => mor y Empty_map Empty_map.
Global Instance: Terminal x := fun y f' => (limit_terminal (Limit:=H1) (CC y) (CCM y f')).

End test.

Section test2.
Context `{Category C} {x: C}.
Context `{Terminal _ _ x}.

Let CC (y: C) : cone.Object (X:=Empty_map:Empty_set→C) (X':=Empty_map) :=  (cone.object y Empty_map Empty_map).
Let CCM {y: cone.Object (X:=Empty_map:_→C) (X':=Empty_map)} (f: cone.vertex y⟶x) : y ⟶ (CC x) :=  (cone.arrow y (CC x) f Empty_map).
Instance: cone.Cone (x:C) (Empty_map) := Empty_map.
Instance: forall c (f:c⟶x) (c_j:forall j:Empty_set, c ⟶ Empty_map j) `{c_cone:!cone.Cone c c_j}, cone.ConeMorphism (f':=Empty_map) c_cone Empty_map f := fun _ _ _ _ => Empty_map.
Instance: Limit (J:=Empty_set) (Arrows1:=_) (CatComp0:=_) (H:=_) (Arrows0:=_) (X:=Empty_map:_→C) (x:=x) (X':=Empty_map) (x_j:=Empty_map) (mor:=fun c c_j _ => H1 c).
Proof.
econstructor.
intros y f.
apply H2.
Qed.
End test2.
