/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/AP/BasicTests.lean -/


import sympy.atlas.Combinatorics.AP.Basic
import Lemma.Set.APBasic
import Mathlib.Tactic.IntervalCases


example : ([1, 2, 3] : List ℕ).IsAPOfLengthWith 3 1 1 :=
  Or.inl rfl

example : (∅ : Finset ℕ).IsAPOfLengthFree 0 := by
  simp [Finset.IsAPOfLengthFree, Set.IsAPOfLengthFree]

example : (({1, 3, 8} : Finset ℕ) : Set ℕ).IsAPOfLengthFree 3 := by
  apply ThreeAPFree.isAPOfLengthFree_three
  rw [threeAPFree_iff_eq_right]
  norm_num

example : ¬ (({1, 2, 3} : Set ℕ).IsAPOfLengthFree 3) := by
  apply Set.IsAPOfLength.not_isAPOfLengthFree
  · refine ⟨1, 1, ?_⟩
    constructor
    · norm_num [ENat.card]
    · ext x
      constructor
      · rintro (rfl | rfl | rfl)
        · exact ⟨0, by norm_num, by norm_num⟩
        · exact ⟨1, by norm_num, by norm_num⟩
        · exact ⟨2, by norm_num, by norm_num⟩
      · rintro ⟨n, hn, rfl⟩
        have hn' : n < 3 := by exact_mod_cast hn
        interval_cases n <;> norm_num
  · norm_num

example (k n : ℕ) : Set.IsAPOfLengthFree.maxCard k n ≤ n :=
  Set.IsAPOfLengthFree.maxCard_le k n

example (k n : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 n ∧
      S.card = Set.IsAPOfLengthFree.maxCard k n ∧ S.IsAPOfLengthFree k :=
  Set.IsAPOfLengthFree.maxCard_spec k n

example {S : Finset ℕ} {k n : ℕ} (hS : S ⊆ Finset.Icc 1 n)
    (hfree : S.IsAPOfLengthFree k) :
    S.card ≤ Set.IsAPOfLengthFree.maxCard k n :=
  Set.IsAPOfLengthFree.card_le_maxCard hS hfree
