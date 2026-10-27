import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[roth_scaled_approximation_bound](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {x : ℝ}
  (q : ℚ)
  (r : ℕ)
  (a Q : ℝ)
-- given
  (hr : 0 < r)
  (ha : 0 ≤ a)
  (hQ : 0 < Q)
  (hpower : Q ≤ ((q.den : ℝ) ^ r))
  (happrox : |x - (q : ℝ)| < 1 / Real.rpow (q.den : ℝ) a) :
-- imply
  |(q : ℝ) - x| ≤ Real.rpow Q (-a / r) := by
-- proof
  have hden : (0 : ℝ) ≤ q.den := by positivity
  have happ : |(q : ℝ) - x| ≤ Real.rpow (q.den : ℝ) (-a) := by
    rw [abs_sub_comm]
    refine happrox.le.trans_eq ?_
    calc
      _ = (Real.rpow (q.den : ℝ) a)⁻¹ := by
        rw [one_div]
      _ = Real.rpow (q.den : ℝ) (-a) := (Real.rpow_neg hden a).symm
  have hid : Real.rpow (q.den : ℝ) (-a) =
      Real.rpow ((q.den : ℝ) ^ r) (-a / (r : ℝ)) := calc
    _ = Real.rpow (q.den : ℝ) ((r : ℝ) * (-a / r)) := by
      congr 1
      field_simp
    _ = Real.rpow (Real.rpow (q.den : ℝ) (r : ℝ)) (-a / r) :=
      Real.rpow_mul hden _ _
    _ = Real.rpow ((q.den : ℝ) ^ r) (-a / r) := by
      congr 1
      exact Real.rpow_natCast _ _
  rw [hid] at happ
  exact happ.trans (Real.rpow_le_rpow_of_nonpos hQ hpower
    (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg _)))


-- created on 2026-10-21
