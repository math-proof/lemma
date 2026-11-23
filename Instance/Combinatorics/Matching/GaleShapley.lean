/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Abbrev.Combinatorics.Matching.GaleShapley
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/
@[expose] public section

namespace MathlibExt.Combinatorics.Matching.GaleShapley

namespace StrictTotalOrder

/-- Compatibility instance for the former `GaleShapley` order instance.

For new code, use `MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder` directly. -/
instance isStrictTotalOrder {α : Type*} (T : StrictTotalOrder α) :
    IsStrictTotalOrder α T.lt :=
  MathlibExt.Order.StrictTotalOrder.isStrictTotalOrder T

end StrictTotalOrder
end MathlibExt.Combinatorics.Matching.GaleShapley
