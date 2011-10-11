Require Import Utf8.
Require Import
  abstract_algebra.
Require Import theory.setoids.
Require Import interfaces.functors.
Require Import extra_tactics.

Notation ArrowsEquiv C :=  (forall x y : C, Equiv (x ⟶ y)).

Section functor_arrows.
  Context `{Category C} `{Category D} (map_obj: C → D).

  Global Instance FunctorArrows : Arrows (C → D) :=
    λ F G, ∀ X Y:C, (X ⟶ Y) → (F X) ⟶ (G Y).

  Global Instance FunctorArrowsEquiv : ArrowsEquiv (C → D) :=
      λ F G alpha beta, ∀ X Y:C,
        (equiv ==> equiv)%signature (alpha X Y) (beta X Y).

End functor_arrows.
Implicit Arguments FunctorArrows [[C][D]].

Require dual.

Delimit Scope functor_signature_scope with functor_signature.

Inductive FunctorSignature :=
  | category_signature C `{Arrows C} `{ArrowsEquiv C} `{!CatId C, !CatComp C}
  |   functor_signature C `{Arrows C} `{ArrowsEquiv C} `{!CatId C, !CatComp C} (target: FunctorSignature)
  | cofunctor_signature C `{Arrows C} `{ArrowsEquiv C} `{!CatId C, !CatComp C} (target: FunctorSignature).
Bind Scope functor_signature_scope with FunctorSignature.

Notation "[| C |]" := (category_signature C) : functor_signature_scope.
Notation "[| C |] ++> D" :=
  (functor_signature C (D%functor_signature))
  (right associativity, at level 55) : functor_signature_scope.
Notation "[| C |] --> D" :=
  (cofunctor_signature C (D%functor_signature))
  (right associativity, at level 55) : functor_signature_scope.

Fixpoint make_ob_sig (sig: FunctorSignature) :=
  match sig with
    | category_signature C _ _ _ _ => C
    | functor_signature C _ _ _ _ D => C → make_ob_sig D
    | cofunctor_signature C _ _ _ _ D => C → make_ob_sig D
  end.

Coercion make_ob_sig: FunctorSignature >-> Sortclass.

Fixpoint make_arrow_sig (sig: FunctorSignature) : Arrows (sig) :=
  match sig as sig return Arrows (sig) with
    | category_signature C A _ _ _ => @Arrow C A
    | functor_signature C A _ _ _ D => λ F G, ∀ X Y: C, (X ⟶ Y) → ((F X) ⟶ (G Y))
    | cofunctor_signature C A _ _ _ DD => λ F G, ∀ X Y: C, (Y ⟶ X) → ((F X) ⟶ (G Y))
  end.

Existing Instance make_arrow_sig.

Class M_Fmap (sig: FunctorSignature) (F: sig) : Type := m_fmap: F ⟶ F.
(* This means that given the signature [|C|], and an element of the signature F (just an object)
   an arrow from F --> F is just an endomorphism of that object. *)
Implicit Arguments m_fmap [[sig][M_Fmap]].

Fixpoint preserves_id_statement (sig: FunctorSignature) : ∀ F {fmap: M_Fmap sig F}, Prop :=
  match sig as sig return ∀ (F: sig) (fmap: M_Fmap sig F), Prop with
    | category_signature C _ e _ _ =>
       λ F fmap, (@equiv _ (e _ _)) fmap cat_id
    | functor_signature C A e _ _ D => λ F fmap, ∀ (X: C) f,
        (@equiv _ (e _ _)) f cat_id → preserves_id_statement D (F X) (fmap X X f)
    | cofunctor_signature C _ e _ _ D => λ F fmap, ∀ (X: C) f,
        (@equiv _ (e _ _)) f cat_id → preserves_id_statement D (F X) (fmap X X f)
  end.
Implicit Arguments preserves_id_statement [[fmap]].

Class PreservesId (sig: FunctorSignature) (F:sig) `{fmap: !M_Fmap sig F} := preserves_id : preserves_id_statement sig F.

Obligation Tactic := idtac.
Program Fixpoint preserves_comp_hetero_statement (sig: FunctorSignature) : ∀ {F G H: sig} (alpha: F⟶H) (beta: G⟶H) (gamma: F⟶G), Prop :=
  match sig as sig return ∀ (F G H: sig) (alpha: F ⟶ H) (beta: G ⟶ H) (gamma: F ⟶ G), Prop with
    | category_signature C A e id cat_comp => λ (F G H: C) alpha beta gamma,
        alpha = (comp F G H beta gamma)
    |   (functor_signature C A e _ _ D)  => λ (F G H: (alpha: @Arrow sig _ F H) beta gamma, ∀ (X Y Z: C) (f: X ⟶ Z) (g: Y ⟶ Z) (h: X ⟶ Y),
          f = (comp X Y Z g h) → preserves_comp_hetero_statement D (F X)(G Y)(H Z) (alpha X) _ _
    | cofunctor_signature C A e _ _ D => λ F G H alpha beta gamma, ∀ (X Y Z: C) (f: X ⟶ Z) (g: Y ⟶ Z) (h: X ⟶ Y), True
  end.
Next Obligation. intros; apply (alpha _ _ f). Defined.
Next Obligation. intros; apply (beta _ _ g). Defined.
Next Obligation. intros; apply (gamma _ _ h). Defined.
Print preserves_comp_hetero_statement.
Print preserves_comp_hetero_statement_obligation_1.
  simpl in *.
  apply alpha.

        (@equiv _ (e _ _)) f (comp X Y Z g  h) → preserves_comp_hetero_statement D (F X) (G Y) (H Z) (alpha _ _ f) (beta _ _ g) (gamma _ _ h)
       end.
    | cofunctor_signature C _ _ _ _ D => λ F G H alpha beta gamma, ∀ X Y Z (f: Z ⟶ X) (g: Y ⟶ X) (h: Z ⟶ Y),
        preserves_comp_hetero_statement C Z Y X f g h → preserves_comp_hetero_statement D _ _ _ (alpha _ _ f) (beta _ _ h) (gamma _ _ g)
  end.
Implicit Arguments preserves_comp_hetero_statement [[F][G][H]].

Definition preserves_comp_statement (sig: FunctorSignature) (F: sig) (fmap: M_Fmap sig F): Prop := preserves_comp_hetero_statement sig fmap fmap fmap.

Class PreservesComp (sig: FunctorSignature) (F: sig) `{fmap: !M_Fmap sig F} : Prop :=
| preserves_comp: preserves_comp_statement sig F fmap.

Section Statement_tests.

Variable C D E:Type.
Context `{!Arrows C} `{!Arrows D} `{!Arrows E}
  `{!CatId C} `{!CatId D} `{!CatId E}
  `{!CatComp C} `{!CatComp D} `{!CatComp E}
  `{!ArrowsEquiv C} `{!ArrowsEquiv D} `{!ArrowsEquiv E}.

Eval compute in (M_Fmap ([|C|] ++> [|D|])).
Eval compute in (preserves_id_statement ([|C|] ++> [|D|])).
Eval compute in (M_Fmap ([|C|] --> [|D|] ++> [|E|])).
Eval compute in (preserves_id_statement ([|C|] --> [|D|] ++> [|E|])).

Eval compute in (preserves_comp_statement ([|C|] ++> [|D|]))%functor_signature.
Eval compute in (preserves_comp_statement ([|C|] --> [|D|] ++> [|E|])).

Eval compute in (M_Fmap (([|C|] ++> [|D|]) ++> [|E|])).
Eval compute in (preserves_id_statement (([|C|] ++> [|D|]) ++> [|E|])).
Eval compute in (preserves_comp_statement (([|C|] ++> [|D|]) ++> [|E|])).

End Statement_tests.


Fixpoint make_arrow_sig_equiv (sig: FunctorSignature): ArrowsEquiv sig :=
  match sig as sig return ArrowsEquiv sig with
    | category_signature C _ e _ _ =>
       (e:ArrowsEquiv C)
    | functor_signature C D =>
      λ F G alpha beta,
      ∀ (X Y: C) (f g: X⟶Y) ,
      (@equiv _ (make_arrow_sig_equiv C X Y)) f g →
      (@equiv _ (make_arrow_sig_equiv D (F X) (G Y))) (alpha X Y f) (beta X Y g)
    | cofunctor_signature C D =>
      λ F G alpha beta,
      ∀ (X Y: C) (f g: Y⟶X) ,
      make_arrow_sig_equiv C Y X f g →
      make_arrow_sig_equiv D (F X) (G Y) (alpha X Y f) (beta X Y g)
  end.
Existing Instance make_arrow_sig_equiv.

(*
Class FunctorProper (sig:Arrows C) {equivC:ArrowsEquiv C}
  F `{!Fmap sig F} : Prop :=
| functor_proper :> Proper (equivC _ _) (fmap F).
Implicit Arguments functor_proper [[C][sig][equivC][Fmap0][FunctorProper]].
*)

Class M_Functor (sig: FunctorSignature) (F: sig) `(!M_Fmap sig F): Prop :=
    { functor_proper :> Proper (equiv) (m_fmap F)
    ; functor_preserves_id :> PreservesId sig F
    ; funtros_preserves_comp :> PreservesComp sig F }.

Section fun_to_m_fun.
  Context `{Category C} `{Category D} `{!Functor (F: C→D) F'}.

  Instance: M_Fmap ([|C|]++>[|D|]) F := F'.
  Instance: M_Functor ([|C|]++>[|D|]) F F' := {}.
  Proof.
    * repeat intro.
      hyp_rewrite.
      reflexivity.
    * repeat intro.
      hyp_rewrite.
      apply functors.preserves_id.
      typeclasses eauto.
    * repeat intro.
      hyp_rewrite.
      apply functors.preserves_comp.
      typeclasses eauto.
  Qed.
End fun_to_m_fun.
Section m_fun_to_fun.
  Context `{Category C} `{Category D} `{!M_Functor ([|C|]++>[|D|]) (F: C→D) F'}.

  Global Instance: Fmap F := F'.
  Global Instance: Functor F _ := {}.
  Proof.
    * constructor; try typeclasses eauto.
      repeat intro.
      apply (functor_proper (M_Fmap0:=F')).
      assumption.
    * intro; apply (preserves_id (fmap:=F')).
      reflexivity.
    * intros; apply (preserves_comp (fmap:=F')).
      reflexivity.
  Qed.
End m_fun_to_fun.

Section x.
  (* Context `{Category C, Category D, Category E}. *)
  Context `{!M_Functor (C++>D++>E) F F'}.

  Context {c: C}.
  Global Instance: M_Fmap (D++>E) (F c) := F' c c _.
  Abort.
  Global Instance: M_Functor ([|D|]++>[|E|]) (F c) _ := {}.
  Proof.
    * repeat intro.
      apply (functor_proper (M_Fmap0:=F'));
        assumption || reflexivity.
    * intro; apply (preserves_id (fmap:=F'));
        reflexivity.
    * intro; apply (preserves_comp (fmap:=F')).
      symmetry; apply left_identity.
  Qed.
End x.

Require categories.functors.
Section bi_m_fun_to_fun.
  Context `{Category C} `{Category D} `{Category E}
          `{!M_Functor ([|C|]++>[|D|]++>[|E|]) F F'}.

  Set Typeclasses Debug.
  Definition curry (c: C) := functors.object (F c).
Require Import theory.categories.
  Definition curry_map (c c': C) (f: c⟶c') (d: D) :=
    m_fmap F _ _ f d d cat_id.
  Instance: NaturalTransformation (curry_map c d f).
  Proof.
    repeat intro.
(*    unfold curry_map, fmap.
    unfold Fmap_instance_0, m_fmap.
    unfold M_Fmap_instance_1.*)
    transitivity (F' _ _ f _ _ f0) ; [symmetry|idtac].
     - refine (preserves_comp (fmap:=F') _ _ _ f f cat_id _ _ _ _ f0 cat_id f0 _).
       + symmetry; apply right_identity.
       + symmetry; apply left_identity.
     - refine (preserves_comp (fmap:=F') _ _ _ f cat_id f _ _ _ _ f0 f0 cat_id _).
       + symmetry; apply left_identity.
       + symmetry; apply right_identity.
  Qed.
  Instance: M_Fmap ([|C|]++>[|_|]) curry := λ c c' f, functors.arrow (curry c) (curry c')
    (curry_map _ _ f) _.
  Instance: M_Functor ([|C|]++>[|_|])  curry _ := {}.
  Proof.
    * repeat intro.
      apply (functor_proper (M_Fmap0:=F'));
        assumption || reflexivity.
    * repeat intro; apply (preserves_id (fmap:=F'));
        assumption || reflexivity.
    * repeat intro; apply (preserves_comp (fmap:=F')).
      - assumption.
      - symmetry; apply left_identity.
  Qed.
End bi_m_fun_to_fun.

(* The usual notational convention for functor application is to use the
name of the functor to refer to both its object map and its arrow map, relying
on additional conventions regarding object/arrow names for disambiguation
(i.e. "F x" and "F f" map an object and an arrow, respectively, because
"x" and "f" are conventional names for objects and arrows, respectively.

In Coq, for a term F to function as though it had two different types
simultaneously (namely the object map and the arrow map), there must
either (1) be coercions from the type of F to either function, or (2) F must
be (coercible to) a single function that is able to consume both object and
arrow arguments. The following snippet shows that (1) doesn't appear to be
supported in Coq:

  Section test.
    Context (A B: Type).
    Record R := { Ra:> A → unit; Rb:> B → unit }.
    Variables (r: R) (a: A) (b: B).
    Check (r a). (* ok so far *)
    Check (r b). (* Error: The term "b" has type "B" while it is expected to have type "A". *)
  End test.

And even if this /did/ work, we could not use it, because leaving
computational components unbundled is a key aspect of our approach.

For (2), if it could be made to work at all (which is not clear at all), F would need
a pretty egregious type considering that arrow types are indexed by objects,
and that the type of the arrow map (namely "∀ x y, (x ⟶ y) → (F x ⟶ F y)")
must refer to the object map.
y
We feel that these issues are not limitations of the Coq system, but merely
reflect the fact that notationally identifying these two different and interdependent
maps is a typical example of an "abus de notation" that by its very nature
is ill-suited to a formal development where software engineering concerns apply.

Hence, we do not adopt this practice, and use "fmap F" (name taken from the Haskell
standard library) to refer to the arrow map of a functor F.

TODO: Sharpen. *)

Section id_functor.
  Context `{Category C}.

  Global Instance: Fmap ([|C|]++>[|C|]) id := λ _ _, id.

  Global Instance id_functor: Functor ([|C|]++>[|C|]) id _.
  Proof.
    constructor; compute; auto || reflexivity.
  Qed.

End id_functor.

Section compose_functors.
  Context
    A B C
    `{!Arrows A} `{!Arrows B} `{!Arrows C}
    `{!CatId A} `{!CatId B} `{!CatId C}
    `{!CatComp A} `{!CatComp B} `{!CatComp C}
    `{∀ x y: A, Equiv (x ⟶ y)}
    `{∀ x y: B, Equiv (x ⟶ y)}
    `{∀ x y: C, Equiv (x ⟶ y)}
    `{!Category A} `{!Category B} `{!Category C}
    `{!Functor ([|B|]++>[|C|]) f f'} `{!Functor ([|A|]++>[|B|]) g g'}.

  Instance comp_Fmap: Fmap ([|A|]++>[|C|]) (f ∘ g) := λ _ _, fmap f _ _ ∘ fmap g _ _.
  Global Instance compose_functors: Functor ([|A|]++>[|C|]) (f ∘ g) _.
  Proof with intuition; try apply _.
   constructor; unfold fmap, comp_Fmap, compose.
   * repeat intro.
     apply (functor_proper (F:=f)).
     apply (functor_proper (F:=g)).
     assumption.
   * simpl. intros.
     apply (preserves_id (F:=f)).
     apply (preserves_id (F:=g)).
     assumption.
   * red. red. simpl. intros.
     apply (preserves_comp (F:=f)).
     apply (preserves_comp (F:=g)).
     assumption.
  Qed.

End compose_functors.

Hint Extern 3 (Fmap (_ ∘ _)) => class_apply comp_Fmap: typeclass_instances.

(** The Functor class is nice and abstract and theory-friendly, but not as convenient
 to use for regular programming as Haskell's Functor class. The reason for this is that
 our Functor is parameterized on two Categories, which by necessity bundle setoid-
 ness and setoid-morphism-ness into objects and arrows, respectively.
 The Haskell Functor class, by contrast, is essentially specialized for endofunctors on
 the category of Haskell types and functions between them. The latter corresponds to our
 setoid.Object category.

 To recover convenience, we introduce a second functor type class tailored specifically to
 functors of this kind. The specialization allows us to forgo bundling, and lets us recover
 the down-to-earth Type→Type type for the type constructor, and the (a→b)→(F a→F b)
 type for the function map, with all setoid/morphism proofs hidden in the structure class
 in Prop.

 To justify this definition, in theory/functors we show that instances of this new functor
 class do indeed give rise to instances of the original nice abstract Functor class. *)

Section setoid_functor.
  Context (map_obj: Type → Type) {map_eq: ∀ `{Equiv A}, Equiv (map_obj A)}.

  Class SFmap: Type := sfmap: ∀ `(v → w), (map_obj v → map_obj w).

  Class SFunctor `{SFmap}: Prop :=
    { sfunctor_makes_setoids `{Setoid A}: Setoid (map_obj A)
    ; sfunctor_makes_morphisms `{Equiv v} `{Equiv w} (f: v → w):>
        Setoid_Morphism f → Setoid_Morphism (sfmap f)
    ; sfunctor_morphism `{Setoid v} `{Setoid w}:>
        Proper (((=) ==> (=)) ==> ((=) ==> (=))) (@sfmap _ v w)
    ; sfunctor_id `{Setoid v}: sfmap id = id
    ; sfunctor_comp `{Equiv a} `{Equiv b} `{Equiv c} (f: b → c) (g: a → b):
        Setoid_Morphism f → Setoid_Morphism g →
        sfmap (f ∘ g) = sfmap f ∘ sfmap g }.

End setoid_functor.
