/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Strict total order modelling strict preference, reusing the shared `MathlibExt.Order` bundle. -/
abbrev StrictTotalOrder := MathlibExt.Order.StrictTotalOrder

namespace StrictTotalOrder

/-- Compatibility alias for the former `GaleShapley.StrictTotalOrder.mk` constructor.

For new code, use `MathlibExt.Order.StrictTotalOrder.mk` directly. -/
abbrev mk {α : Type*} (lt : α → α → Prop)
    (irrefl : ∀ a, ¬lt a a)
    (trans : ∀ {a b c}, lt a b → lt b c → lt a c)
    (total : ∀ {a b}, a ≠ b → lt a b ∨ lt b a) :
    StrictTotalOrder α :=
  MathlibExt.Order.StrictTotalOrder.mk lt irrefl trans total

/-- Compatibility alias for the former `GaleShapley.StrictTotalOrder.lt` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.lt` directly. -/
abbrev lt {α : Type*} (self : StrictTotalOrder α) : α → α → Prop :=
  MathlibExt.Order.StrictTotalOrder.lt self

/-- Compatibility alias for the former `GaleShapley.StrictTotalOrder.irrefl` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.irrefl` directly. -/
abbrev irrefl {α : Type*} (self : StrictTotalOrder α) (a : α) : ¬self.lt a a :=
  MathlibExt.Order.StrictTotalOrder.irrefl self a

/-- Compatibility alias for the former `GaleShapley.StrictTotalOrder.trans` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.trans` directly. -/
abbrev trans {α : Type*} (self : StrictTotalOrder α) {a b c : α}
    (h1 : self.lt a b) (h2 : self.lt b c) : self.lt a c :=
  MathlibExt.Order.StrictTotalOrder.trans self h1 h2

/-- Compatibility alias for the former `GaleShapley.StrictTotalOrder.total` projection.

For new code, use `MathlibExt.Order.StrictTotalOrder.total` directly. -/
abbrev total {α : Type*} (self : StrictTotalOrder α) {a b : α} (h : a ≠ b) :
    self.lt a b ∨ self.lt b a :=
  MathlibExt.Order.StrictTotalOrder.total self h

end StrictTotalOrder
end MathlibExt.Combinatorics.Matching.GaleShapley
