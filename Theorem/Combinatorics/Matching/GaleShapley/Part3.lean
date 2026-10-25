/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part3
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- Case analysis on the woman's choice. -/
lemma womanChoice_spec {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) :
    (o = none ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 = m ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m m1 ∧ womanChoice T o m = m) ∨
    (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m1 m ∧ womanChoice T o m = m1) := by
  unfold womanChoice
  exact Classical.choose_spec (womanChoice_exists T o m)

end MathlibExt.Combinatorics.Matching.GaleShapley
