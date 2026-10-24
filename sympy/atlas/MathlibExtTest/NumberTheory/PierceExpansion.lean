/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PierceExpansion.lean -/


import sympy.atlas.NumberTheory.PierceExpansion
import Lemma.Nat.PierceExpansion
import Mathlib.Tactic.IntervalCases

/-!
# Tests for Pierce expansion trajectories
-/


example : PierceExpansion.traj 7 3 0 = 3 := rfl

example : PierceExpansion.traj 7 3 1 = 1 := rfl

example : PierceExpansion.traj 7 3 2 = 0 := rfl

example : PierceExpansion.length 7 3 = 2 := by
  apply le_antisymm
  · exact PierceExpansion.length_le_of_traj_eq_zero (by decide) rfl
  · by_contra hlt
    have hlt' : PierceExpansion.length 7 3 < 2 := lt_of_not_ge hlt
    have h1 := PierceExpansion.length_pos 7 3
    have heq : PierceExpansion.length 7 3 = 1 := by omega
    have h0 := PierceExpansion.traj_length_eq_zero 7 3
    rw [heq] at h0
    exact absurd h0 (by decide)

example : PierceExpansion.maxLength 3 = 2 := by
  apply le_antisymm
  · apply PierceExpansion.maxLength_le_of_forall
    intro a ha
    rw [Finset.mem_Icc] at ha
    obtain ⟨ha1, ha2⟩ := ha
    interval_cases a
    · exact PierceExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
    · exact PierceExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
    · exact PierceExpansion.length_le_of_traj_eq_zero (j := 2) (by decide) rfl
  · have h2 : PierceExpansion.length 3 2 = 2 := by
      apply le_antisymm
      · exact PierceExpansion.length_le_of_traj_eq_zero (by decide) rfl
      · by_contra hlt
        have hlt' : PierceExpansion.length 3 2 < 2 := lt_of_not_ge hlt
        have h1 := PierceExpansion.length_pos 3 2
        have heq : PierceExpansion.length 3 2 = 1 := by omega
        have h0 := PierceExpansion.traj_length_eq_zero 3 2
        rw [heq] at h0
        exact absurd h0 (by decide)
    have hmem : 2 ∈ Finset.Icc 1 3 := by decide
    have hle := PierceExpansion.length_le_maxLength hmem
    omega
