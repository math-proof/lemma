/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/EngelExpansion.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat
import Def.NumberTheory.EngelExpansion.Part2
/-!
# Engel expansion trajectories

Remainder trajectories and length functions for Engel expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Engel trajectory starts at `a` and iterates `t ↦ (-n) % t`
until reaching `0`; its length is the length of the Engel expansion of `a / n`.
-/


namespace EngelExpansion

/-- Every Engel trajectory reaches `0` within `a + 1` steps. -/
theorem exists_traj_eq_zero (n a : ℕ) : ∃ i ≤ a + 1, traj n a i = 0 := by
  have key : ∀ j, traj n a j ≤ a - j ∨ ∃ i ≤ j, traj n a i = 0 := by
    intro j
    induction j with
    | zero => exact Or.inl (by simp [traj])
    | succ j ih =>
        rcases ih with hle | ⟨i, hij, hi0⟩
        · by_cases hj0 : traj n a j = 0
          · exact Or.inr ⟨j, Nat.le_succ j, hj0⟩
          · have hlt : negRem n (traj n a j) < traj n a j :=
              negRem_lt hj0
            have hle2 : negRem n (traj n a j) ≤ a - (j + 1) := by
              revert hlt
              generalize negRem n (traj n a j) = m
              intro hlt
              omega
            have hstep : traj n a (j + 1) = negRem n (traj n a j) := by
              simp only [traj, ite_eq_right hj0]
            have hfin : traj n a (j + 1) ≤ a - (j + 1) := by
              rw [hstep]
              exact hle2
            exact Or.inl hfin
        · exact Or.inr ⟨i, le_trans hij (Nat.le_succ j), hi0⟩
  rcases key (a + 1) with hle | hex
  · have h0 : traj n a (a + 1) = 0 := by omega
    exact ⟨a + 1, le_refl _, h0⟩
  · exact hex

/-- Every Engel trajectory hits `0` at some positive step. -/
theorem exists_traj_eq_zero_pos (n a : ℕ) : ∃ j ≥ 1, traj n a j = 0 := by
  rcases exists_traj_eq_zero n a with ⟨i, _, hi0⟩
  refine ⟨i + 1, Nat.succ_le_succ (Nat.zero_le i), ?_⟩
  simp [traj, hi0]

end EngelExpansion
