/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Theorem.Combinatorics.Matching.GaleShapley
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/
public section




namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Deferred-acceptance state. -/
structure DAState (M W : Type*) where
  prop : M → Finset W
  hold : W → Option M

end MathlibExt.Combinatorics.Matching.GaleShapley
