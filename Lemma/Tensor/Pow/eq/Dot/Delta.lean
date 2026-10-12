import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {z : ℝ} :
-- imply
  z ^ n = ∑ i ∈ Finset.range (n + 1), z ^ i * (if i = n then 1 else 0) := by
-- proof
  rw [Finset.sum_eq_single n (fun i _ hi => by rw [ite_eq_right hi, mul_zero]) (fun h => absurd (Finset.self_mem_range_succ n) h),
    ite_eq_left rfl, mul_one]


-- created on 2023-08-26
