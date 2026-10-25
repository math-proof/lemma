/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Series/HardyInequality.lean -/


import sympy.atlas.Analysis.Series.HardyInequality


namespace MetaMathlibExt

-- The first conclusion supplies summability of the prefix-average powers.
example {a : ℕ → ℝ} {p : ℝ} (hp : 1 < p) (hnonneg : ∀ n, 0 ≤ a n)
    (hsumm : Summable fun n ↦ (a n).rpow p) :
    Summable fun n ↦
      ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow p) :=
  (hardy_inequality hp hnonneg hsumm).1

-- At `p = 2`, the sharp Hardy constant is `4`.
example {a : ℕ → ℝ} (hnonneg : ∀ n, 0 ≤ a n)
    (hsumm : Summable fun n ↦ (a n).rpow (2 : ℝ)) :
    ∑' n, ((Finset.sum (Finset.range (n + 1)) a / ((n : ℝ) + 1)).rpow (2 : ℝ)) ≤
      4 * ∑' n, (a n).rpow (2 : ℝ) := by
  have h := (hardy_inequality (p := (2 : ℝ)) (by norm_num) hnonneg hsumm).2
  norm_num [Real.rpow_natCast, Real.rpow_eq_pow] at h ⊢
  exact h

end MetaMathlibExt
