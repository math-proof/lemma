import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {z : ℝ} :
-- imply
  z ^ n = ∑ i ∈ Finset.range (n + 1), z ^ i * (if i = n then 1 else 0) := by
-- proof
  rw [Finset.sum_eq_single n (fun i _ hi => by rw [if_neg hi, mul_zero]) (fun h => absurd (Finset.self_mem_range_succ n) h),
    if_pos rfl, mul_one]


-- created on 2023-08-26
