/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SocialChoice/Arrow.lean -/

import Mathlib.Data.Fintype.Basic
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.SuccPred


section

namespace MathlibExt.GameTheory.SocialChoice.ArrowWanted

/-! # Arrow's impossibility theorem

Records Pareto and IIA for social welfare functions over strict total orders.
-/

/-- Strict total order for strict preference, reusing the shared `MathlibExt.Order` bundle. -/
abbrev StrictTotalOrder := MathlibExt.Order.StrictTotalOrder

namespace StrictTotalOrder

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.mk` constructor.

For new code, use `MathlibExt.Order.StrictTotalOrder.mk` directly. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.lt` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.lt` directly. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.irrefl` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.irrefl` directly. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.trans` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.trans` directly. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- Compatibility alias for the former `ArrowWanted.StrictTotalOrder.total` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.total` directly. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder

/-- A profile assigns each voter a strict total order over alternatives. -/
abbrev Profile (Alt Voter : Type*) := Voter → StrictTotalOrder Alt

/-- A social welfare function maps each unrestricted profile to a social strict total order. -/
abbrev SocialWelfareFunction (Alt Voter : Type*) := Profile Alt Voter → StrictTotalOrder Alt

end MathlibExt.GameTheory.SocialChoice.ArrowWanted
end
