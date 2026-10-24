/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/EngelExpansion.lean -/


import sympy.atlas.NumberTheory.EngelExpansion
import Lemma.Nat.EngelExpansion
import Mathlib.Tactic.IntervalCases

/-!
# Tests for Engel expansion trajectories
-/


example : EngelExpansion.negRem 7 3 = 2 := rfl

example : EngelExpansion.negRem 6 3 = 0 := rfl

example : EngelExpansion.traj 7 3 0 = 3 := rfl

example : EngelExpansion.traj 7 3 1 = 2 := rfl

example : EngelExpansion.traj 7 3 2 = 1 := rfl

example : EngelExpansion.traj 7 3 3 = 0 := rfl

example : EngelExpansion.length 7 3 = 3 := by
  apply le_antisymm
  · exact EngelExpansion.length_le_of_traj_eq_zero (by decide) rfl
  · by_contra hlt
    have hlt' : EngelExpansion.length 7 3 < 3 := lt_of_not_ge hlt
    have h1 := EngelExpansion.length_pos 7 3
    have hcases : EngelExpansion.length 7 3 = 1 ∨ EngelExpansion.length 7 3 = 2 :=
      by omega
    have h0 := EngelExpansion.traj_length_eq_zero 7 3
    rcases hcases with heq | heq
    · rw [heq] at h0
      exact absurd h0 (by decide)
    · rw [heq] at h0
      exact absurd h0 (by decide)

example : EngelExpansion.maxLength 3 = 2 := by
  apply le_antisymm
  · apply EngelExpansion.maxLength_le_of_forall
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, ha2⟩ := ha
    interval_cases a
    · exact EngelExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
    · exact EngelExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
    · exact EngelExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
  · have h2 : EngelExpansion.length 3 2 = 2 := by
      apply le_antisymm
      · exact EngelExpansion.length_le_of_traj_eq_zero (by decide) rfl
      · by_contra hlt
        have hlt' : EngelExpansion.length 3 2 < 2 := lt_of_not_ge hlt
        have h1 := EngelExpansion.length_pos 3 2
        have heq : EngelExpansion.length 3 2 = 1 := by omega
        have h0 := EngelExpansion.traj_length_eq_zero 3 2
        rw [heq] at h0
        exact absurd h0 (by decide)
    have hmem : 2 ∈ Finset.Icc 1 3 := by decide
    have hle := EngelExpansion.length_le_maxLength hmem
    omega
