/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

module

public import Mathlib.Data.Fintype.Card
public import Instance.Order.StrictTotalOrder
public import Theorem.Set.StrictTotalOrder
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Instance.Combinatorics.Matching.GaleShapley
@[expose] public section

/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Preferences of `M` over `W`. -/
abbrev MPrefs (M W : Type*) := M → StrictTotalOrder W

/-- Preferences of `W` over `M`. -/
abbrev WPrefs (M W : Type*) := W → StrictTotalOrder M

/-- A perfect matching as an equivalence between the two sides. -/
abbrev PerfectMatching (M W : Type*) := M ≃ W

end MathlibExt.Combinatorics.Matching.GaleShapley
