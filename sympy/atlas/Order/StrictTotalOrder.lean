/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Order/StrictTotalOrder.lean -/

import Mathlib.Order.Defs.Unbundled

/-! # Strict total orders

Shared bundle for strict preferences, used by matching and social-choice developments.
-/

namespace MathlibExt.Order

/-- Strict total order modelling strict preference:
irreflexive, transitive, total on distinct elements. -/
structure StrictTotalOrder (α : Type*) where
  lt : α → α → Prop
  irrefl : ∀ a, ¬ lt a a
  trans : ∀ {a b c}, lt a b → lt b c → lt a c
  total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a

/-- The relation of a `StrictTotalOrder` is a strict total order in Mathlib's unbundled sense, so
generic strict-order lemmas apply to `T.lt`. -/
instance StrictTotalOrder.isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt where
  irrefl := T.irrefl
  trans _ _ _ := T.trans
  trichotomous := fun _ _ hab hba =>
    Classical.byContradiction fun h => (T.total h).elim hab hba
end MathlibExt.Order
