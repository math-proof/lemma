/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PierceExpansion.lean -/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Nat.Find
import Mathlib.Order.Interval.Finset.Nat

/-!
# Pierce expansion trajectories

Remainder trajectories and length functions for Pierce expansions of rationals, after
Erdős–Shallit ("New bounds on the length of finite Pierce and Engel series").
For `1 ≤ a ≤ n`, the Pierce trajectory starts at `a` and iterates `t ↦ n % t`
until reaching `0`; its length is the length of the Pierce expansion of `a / n`.
-/

namespace PierceExpansion

/-- Pierce remainder trajectory: `traj 0 = a`, `traj (j+1) = n % traj j`,
absorbing at `0`. -/
def traj (n a : ℕ) : ℕ → ℕ
  | 0 => a
  | j + 1 => if traj n a j = 0 then 0 else n % traj n a j

/-- Unfolding at step zero. -/
theorem traj_zero (n a : ℕ) : traj n a 0 = a :=
  rfl

/-- Unfolding after a vanishing step. -/
theorem traj_succ_of_eq_zero {n a j : ℕ} (h : traj n a j = 0) :
    traj n a (j + 1) = 0 := by
  simp only [traj, ite_eq_left h]

/-- Unfolding after a nonvanishing step. -/
theorem traj_succ_of_ne_zero {n a j : ℕ} (h : traj n a j ≠ 0) :
    traj n a (j + 1) = n % traj n a j := by
  simp only [traj, ite_eq_right h]

/-- First-step computation. -/
theorem traj_one {n t : ℕ} (ht : t ≠ 0) : traj n t 1 = n % t := by
  have h01 : (1 : ℕ) = 0 + 1 := rfl
  have h0 : traj n t 0 ≠ 0 := by
    rw [traj_zero]
    exact ht
  rw [h01, traj_succ_of_ne_zero h0, traj_zero]

/-- Every Pierce trajectory reaches `0` within `a + 1` steps. -/
theorem exists_traj_eq_zero (n a : ℕ) : ∃ i ≤ a + 1, traj n a i = 0 := by
  have key : ∀ j, traj n a j ≤ a - j ∨ ∃ i ≤ j, traj n a i = 0 := by
    intro j
    induction j with
    | zero => exact Or.inl (by simp [traj])
    | succ j ih =>
        rcases ih with hle | ⟨i, hij, hi0⟩
        · by_cases hj0 : traj n a j = 0
          · exact Or.inr ⟨j, Nat.le_succ j, hj0⟩
          · have hlt : n % traj n a j < traj n a j :=
              Nat.mod_lt n (Nat.pos_of_ne_zero hj0)
            have hle2 : n % traj n a j ≤ a - (j + 1) := by
              revert hlt
              generalize n % traj n a j = m
              intro hlt
              omega
            have hstep : traj n a (j + 1) = n % traj n a j := by
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

/-- Every Pierce trajectory hits `0` at some positive step. -/
theorem exists_traj_eq_zero_pos (n a : ℕ) : ∃ j ≥ 1, traj n a j = 0 := by
  rcases exists_traj_eq_zero n a with ⟨i, _, hi0⟩
  refine ⟨i + 1, Nat.succ_le_succ (Nat.zero_le i), ?_⟩
  simp [traj, hi0]

/-- Pierce length: least `j ≥ 1` with `traj j = 0`. This is the length of the Pierce
expansion of `a / n`. -/
noncomputable def length (n a : ℕ) : ℕ :=
  Nat.find (exists_traj_eq_zero_pos n a)

/-- The Pierce length is positive. -/
theorem length_pos (n a : ℕ) : 1 ≤ length n a :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).1

/-- The Pierce trajectory vanishes at the Pierce length. -/
theorem traj_length_eq_zero (n a : ℕ) : traj n a (length n a) = 0 :=
  (Nat.find_spec (exists_traj_eq_zero_pos n a)).2

/-- The Pierce length is bounded by any positive vanishing step. -/
theorem length_le_of_traj_eq_zero {n a j : ℕ} (hj : 1 ≤ j)
    (h : traj n a j = 0) : length n a ≤ j :=
  Nat.find_min' _ ⟨hj, h⟩

/-- The Pierce trajectory is nonzero at positive steps below the length. -/
theorem traj_ne_zero_of_lt_length {n a j : ℕ} (hj : 1 ≤ j)
    (hlt : j < length n a) : traj n a j ≠ 0 := by
  have hneg := Nat.find_min _ hlt
  intro h0
  exact hneg ⟨hj, h0⟩

/-- Pierce length function: `max_{1 ≤ a ≤ n} length n a`. -/
noncomputable def maxLength (n : ℕ) : ℕ :=
  (Finset.Icc 1 n).sup (length n)

/-- Each Pierce length is bounded by the length function. -/
theorem length_le_maxLength {n a : ℕ} (ha : a ∈ Finset.Icc 1 n) :
    length n a ≤ maxLength n :=
  Finset.le_sup ha

/-- The length function is bounded by a uniform bound on all lengths. -/
theorem maxLength_le_of_forall {n L : ℕ}
    (h : ∀ a ∈ Finset.Icc 1 n, length n a ≤ L) : maxLength n ≤ L :=
  Finset.sup_le h

end PierceExpansion
