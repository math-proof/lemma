import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.SpecialFunctions.EntireExponentialIntegral
open Set


namespace Complex

/--
[hasDerivAt_einTerm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma hasDerivAt_einTerm (n : ℕ) (z : ℂ) :
  HasDerivAt (einTerm n)
    ((-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z := by
  unfold einTerm
  have hne1 : ((n + 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hneFac : (((n + 1).factorial : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h := (((hasDerivAt_const z ((-1 : ℂ) ^ n)).mul
    (hasDerivAt_pow (n + 1) z)).div_const
      (((n + 1 : ℕ) : ℂ) * ((n + 1).factorial : ℂ)))
  have hder : (0 * z ^ (n + 1) + (-1 : ℂ) ^ n * (((n + 1 : ℕ) : ℂ) * z ^ (n + 1 - 1))) /
    (((n + 1 : ℕ) : ℂ) * (((n + 1).factorial : ℕ) : ℂ)) =
    (-1 : ℂ) ^ n * z ^ n / (((n + 1).factorial : ℕ) : ℂ) := by
    rw [Nat.add_sub_cancel]
    simp only [zero_mul, zero_add]
    field_simp [hne1, hneFac]
  rwa [hder] at h

end Complex

namespace Complex

/--
[einTerm_deriv_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma einTerm_deriv_norm_le {R : ℝ} {z : ℂ}
  (hz : ‖z‖ < R) (n : ℕ) :
  ‖(-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)‖ ≤
    R ^ n / n.factorial := by
  have hR : 0 ≤ R := le_trans (norm_nonneg z) hz.le
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_one,
    one_pow, one_mul, norm_natCast, Nat.factorial_succ]
  gcongr
  rw [Nat.succ_mul, add_comm]
  exact Nat.le_add_right _ _

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
lemma hasDerivAt_ein
-- given
  (z : ℂ) :
-- imply
  HasDerivAt Complex.ein
    (∑' n : ℕ, (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z := by
-- proof
  let R : ℝ := ‖z‖ + 1
  change HasDerivAt (fun w => ∑' n : ℕ, einTerm n w)
    (∑' n : ℕ,
      (-1 : ℂ) ^ n * z ^ n / ((n + 1).factorial : ℂ)) z
  refine hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => R ^ n / n.factorial)
    (g := einTerm)
    (g' := fun n w =>
      (-1 : ℂ) ^ n * w ^ n / ((n + 1).factorial : ℂ))
    (t := Metric.ball 0 R) (y₀ := 0) (y := z)
    (Real.summable_pow_div_factorial R)
    Metric.isOpen_ball (convex_ball (0 : ℂ) R).isPreconnected ?_ ?_ ?_ ?_ ?_
  · intro n y _hy
    exact hasDerivAt_einTerm n y
  · intro n y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact einTerm_deriv_norm_le hy n
  · simp only [R, Metric.mem_ball, dist_zero_right, norm_zero]
    positivity
  · simp [einTerm]
  · simp [R, Metric.mem_ball]

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
lemma differentiable_ein
-- imply
  Differentiable ℂ Complex.ein :=
-- proof
  fun z => (hasDerivAt_ein z).differentiableAt

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
lemma analyticOnNhd_ein
-- imply
  AnalyticOnNhd ℂ Complex.ein Set.univ :=
-- proof
  analyticOnNhd_univ_iff_differentiable.mpr differentiable_ein

end Complex

namespace Complex

/--
[exp_tail](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
private lemma exp_tail (z : ℂ) :
  (∑' n : ℕ, (-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) =
    Complex.exp (-z) - 1 := by
  have hfull : HasSum (fun n : ℕ => (-z) ^ n / (n.factorial : ℂ))
    (Complex.exp (-z)) := by
    simpa only [← Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℂ) (-z))
  simpa using ((hasSum_nat_add_iff' 1).mpr hfull).tsum_eq

end Complex

namespace Complex

/--
[EntireExponentialIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/EntireExponentialIntegral.lean)
-/
@[path]
lemma mul_deriv_ein
-- given
  (z : ℂ) :
-- imply
  z * deriv Complex.ein z = 1 - Complex.exp (-z) := by
-- proof
  rw [(hasDerivAt_ein z).deriv, ← tsum_mul_left]
  calc
    (∑' n : ℕ,
      z * ((-1 : ℂ) ^ n * z ^ n /
        ((n + 1).factorial : ℂ))) =
      ∑' n : ℕ,
        -((-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) := by
      apply tsum_congr
      intro n
      have hneg : (-z) ^ n = (-1 : ℂ) ^ n * z ^ n :=
        neg_pow z n
      rw [pow_succ, hneg]
      ring
    _ = -(∑' n : ℕ,
      (-z) ^ (n + 1) / ((n + 1).factorial : ℂ)) := by
      rw [tsum_neg]
    _ = 1 - Complex.exp (-z) := by
      rw [exp_tail]
      ring
end



-- created on 2026-10-11
-- updated on 2026-10-26
