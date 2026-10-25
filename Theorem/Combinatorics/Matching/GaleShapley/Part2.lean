/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matching/GaleShapley.lean -/

import Mathlib.Data.Fintype.Card
import Instance.Order.StrictTotalOrder
import Lemma.Set.StrictTotalOrder
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Def.Combinatorics.Matching.GaleShapley.Part2
/-! # Gale–Shapley stable marriage existence

Stable perfect matchings for two equal finite sides with strict total preferences.
-/


namespace MathlibExt.Combinatorics.Matching.GaleShapley

/-- A woman picks between her old holder `o` and a new proposer `m`. -/
lemma womanChoice_exists {M : Type*}
    (T : StrictTotalOrder M) (o : Option M) (m : M) :
    ∃ mstar : M, (o = none ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 = m ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m m1 ∧ mstar = m) ∨
      (∃ m1, o = some m1 ∧ m1 ≠ m ∧ T.lt m1 m ∧ mstar = m1) := by
  cases o with
  | none => exact ⟨m, Or.inl ⟨rfl, rfl⟩⟩
  | some m' =>
    by_cases h1 : m' = m
    · subst m'
      exact ⟨m, Or.inr (Or.inl ⟨m, rfl, rfl, rfl⟩)⟩
    · by_cases h2 : T.lt m m'
      · exact ⟨m, Or.inr (Or.inr (Or.inl ⟨m', rfl, h1, h2, rfl⟩))⟩
      · have h3 : T.lt m' m := by
          rcases T.total h1 with h | h
          · exact h
          · exact absurd h h2
        exact ⟨m', Or.inr (Or.inr (Or.inr ⟨m', rfl, h1, h3, rfl⟩))⟩

end MathlibExt.Combinatorics.Matching.GaleShapley
