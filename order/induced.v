(*Require Import Morphisms.*)
Require Import abstract_algebra.
Require Import interfaces.orders.

Section induced_setoid.
Context S O `{Setoid O} (P : S → O).
Instance induced_equiv: Equiv S | 100 := λ x y, P x = P y.

Hint Extern 0 => unfold equiv, induced_equiv.

Instance induced_Setoid: Setoid S := {}.
Proof. split; auto. Qed.
Global Instance: Setoid_Morphism P := {}.
Proof. auto. Qed.
End induced_setoid.

Hint Extern 4 (@Setoid ?S (@induced_equiv ?S _ _ _)) => apply induced_Setoid : typeclass_instances.

Section induced_order.
Context S O `{PartialOrder O} (P : S → O).
Instance: Setoid O := po_setoid.
Instance induced_le: Le S := λ x y, P x ≤ P y.

Local Hint Extern 4 (Equiv S) => exact (induced_equiv S O P) : typeclass_instances.

Hint Extern 0 => unfold le, induced_le.
Hint Extern 0 => unfold equiv, induced_equiv.

Typeclasses Transparent induced_equiv induced_le.
Print Hint Equiv.

Instance induced_PartialOrder: PartialOrder (A:=S) (≤) := {}.
Proof. auto. auto. auto. Qed.

Global Instance: Order_Morphism P := {}.
Global Instance: OrderPreserving P := {}.
Proof. auto. Qed.
Global Instance: OrderReflecting P := {}.
Proof. auto. Qed.

End induced_order.

Hint Extern 4 (@PartialOrder ?S _ (@induced_le ?S _ _ _)) => apply induced_PartialOrder : typeclass_instances.
