/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Theorem.Combinatorics.Matching.GaleShapley.Part4
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Total number of proposals made so far. -/
def DAMeasure {M W : Type*} [Fintype M] (s : DAState M W) : ℕ :=
  ∑ m ∈ Finset.univ, (s.prop m).card

end MathlibExt.Combinatorics.Matching.GaleShapley
