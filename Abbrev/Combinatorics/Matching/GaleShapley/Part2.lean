/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Instance.Combinatorics.Matching.GaleShapley
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
