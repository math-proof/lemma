module
public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Theorem.Combinatorics.Matching.GaleShapley.Part4


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/
namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Total number of proposals made so far. -/
def DAMeasure {M W : Type*} [Fintype M] (s : DAState M W) : ℕ :=
  ∑ m ∈ Finset.univ, (s.prop m).card

end MathlibExt.Combinatorics.Matching.GaleShapley
