(*Require Import Morphisms.*)
Require Import abstract_algebra.
Require Import interfaces.orders.

Section induced_order.
Context S O `{PartialOrder O} (P : S → O).
Instance: Setoid O := po_setoid.
Instance induced_le: Le S := λ x y, P x ≤ P y.
Instance induced_equiv: Equiv S | 100 := λ x y, P x = P y.

Hint Extern 0 => unfold le, induced_le.
Hint Extern 0 => unfold equiv, induced_equiv.

Global Instance: Setoid S := {}.
Proof. split; auto. Qed.
Global Instance: Setoid_Morphism P := {}.
Proof. auto. Qed.

Typeclasses Transparent induced_equiv induced_le.

Global Instance: PartialOrder (A:=S) (≤) := {}.
Proof. auto. auto. auto. Qed.

Global Instance: Order_Morphism P := {}.
Global Instance: OrderPreserving P := {}.
Proof. auto. Qed.
Global Instance: OrderReflecting P := {}.
Proof. auto. Qed.

End induced_order.
