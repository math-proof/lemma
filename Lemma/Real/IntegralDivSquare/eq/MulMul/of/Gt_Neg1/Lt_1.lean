import Lemma.Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1
import Lemma.Real.HasDerivAt.MulAddDivSinMulAtan.of.Gt_Neg1.Lt_1.Gt_Neg1.Lt_1.Eq
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import sympy.Basic
open Real


/--
Area of an ellipse from its focal polar equation \(r=\dfrac{p}{1-e\cos\varphi}\), \(|e|<1\):
\[
\int_0^{2\pi}\frac12 r^2\,d\varphi=\pi\cdot\frac{p}{1-e^2}\cdot\frac{p}{1-e^2}\sqrt{1-e^2}=\pi ab,
\]
with \(a=\dfrac{p}{1-e^2}\) and \(b=a\sqrt{1-e^2}\).
-/
@[path]
private lemma main
  {e p : ℝ}
-- given
  (he₀ : -1 < e)
  (he₁ : e < 1) :
-- imply
  ∫ x in (0 : ℝ)..2 * π, (p / (1 - e * Real.cos x)) ^ 2 / 2 =
    π * (p / (1 - e ^ 2)) * (p / (1 - e ^ 2) * Real.sqrt (1 - e ^ 2)) := by
-- proof
  have h₀ : 0 < 1 - e ^ 2 := by nlinarith
  set s := Real.sqrt (1 - e ^ 2) with hs
  have hs₀ : 0 < s := Real.sqrt_pos.mpr h₀
  have hss : s ^ 2 = 1 - e ^ 2 := Real.sq_sqrt h₀.le
  -- e = 2 q / (1 + q ^ 2) with q = e / (1 + s)
  set q := e / (1 + s) with hq
  have h1s : 1 + s ≠ 0 := by positivity
  have hq2 : q ^ 2 = (1 - s) / (1 + s) := by
    rw [hq]
    field_simp
    nlinarith
  have hs₁ : s < 1 ∨ s = 1 := by
    have : s ^ 2 ≤ 1 := by nlinarith
    rcases lt_or_eq_of_le (show s ≤ 1 by nlinarith) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hq2lt : q ^ 2 < 1 := by
    rw [hq2, div_lt_one (by positivity)]
    linarith
  have hq₀ : -1 < q := by nlinarith
  have hq₁ : q < 1 := by nlinarith
  have hrel : e * (1 + q ^ 2) = 2 * q := by
    rw [hq2, hq]
    field_simp
    nlinarith
  have hderiv := fun x : ℝ =>
    Real.HasDerivAt.MulAddDivSinMulAtan.of.Gt_Neg1.Lt_1.Gt_Neg1.Lt_1.Eq (p := p) he₀ he₁ hq₀ hq₁ hrel x
  have hcont : Continuous fun x : ℝ => (p / (1 - e * Real.cos x)) ^ 2 / 2 := by
    refine Continuous.div_const (Continuous.pow (Continuous.div continuous_const ?_ ?_) 2) 2
    · fun_prop
    · intro x
      exact (Real.Gt_0Sub1MulCos.of.Gt_Neg1.Lt_1 he₀ he₁ x).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
    (hcont.intervalIntegrable _ _)]
  simp only [Real.sin_zero, Real.cos_zero, Real.sin_two_pi, Real.cos_two_pi]
  simp
  have h1q : 1 - q ^ 2 ≠ 0 := by nlinarith
  have hqs : (1 + q ^ 2) / (1 - q ^ 2) = 1 / s := by
    have hq3 : q ^ 2 * (1 + s) = 1 - s := by
      rw [hq2]
      field_simp
    rw [div_eq_div_iff h1q hs₀.ne']
    linear_combination hq3
  rw [hqs]
  have : 1 - e ^ 2 = s ^ 2 := hss.symm
  rw [this]
  field_simp


-- created on 2026-09-29