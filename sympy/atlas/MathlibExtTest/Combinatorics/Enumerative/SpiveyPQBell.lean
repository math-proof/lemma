/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/SpiveyPQBell.lean -/


import all MathlibExt.Combinatorics.Enumerative.SpiveyPQBell
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt

-- At `p = 1` and `q = 1/2`, the theorem computes `tildeB 2 1` as `3/2`.
example :
    let bracket : ℕ → ℝ := fun k => (1 ^ k - (1 / 2 : ℝ) ^ k) / (1 - 1 / 2)
    let S := spivey_pq_bell.S 1 (1 / 2) bracket
    let tildeS : ℕ → ℕ → ℝ := fun n k => 1 ^ Nat.choose k 2 * S n k
    let tildeB : ℕ → ℝ → ℝ :=
      fun n x => ∑ k ∈ Finset.range (n + 1), tildeS n k * x ^ k
    tildeB 2 1 = 3 / 2 := by
  dsimp only
  have hq0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hqp : (1 / 2 : ℝ) < 1 := by norm_num
  have hp1 : (1 : ℝ) ≤ 1 := by norm_num
  have h := spivey_pq_bell (1 : ℝ) (1 / 2) hq0 hqp hp1 1 1
  dsimp only at h
  rw [h]
  norm_num [Finset.sum_range_succ, spivey_pq_bell.S.eq_1, spivey_pq_bell.S.eq_2]

end MetaMathlibExt
