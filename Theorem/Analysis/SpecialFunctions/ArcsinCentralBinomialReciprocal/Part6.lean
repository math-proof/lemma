import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part7


namespace MetaMathlibExt

theorem hasDerivAt_H1 (x : ℝ) (hx : |x| < 1) : HasDerivAt H1fun (H2fun x) x := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  obtain ⟨hne1, hnem1⟩ := hne_one_of_mem x hx
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  -- inner sqrt derivative
  have h_inner : HasDerivAt (fun y => (1:ℝ) - y ^ 2) (-2 * x) x := by
    have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      have h := hasDerivAt_pow 2 x
      refine h.congr_deriv ?_
      push_cast
      ring
    have h2 : HasDerivAt (fun _ : ℝ => (1:ℝ)) 0 x := hasDerivAt_const x 1
    have h3 := h2.sub h1
    refine h3.congr_deriv ?_
    ring
  have h_sqrt : HasDerivAt (fun y => Real.sqrt (1 - y ^ 2)) ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2))) x :=
    h_inner.sqrt hne
  have h_arcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
    have h := Real.hasDerivAt_arcsin hnem1 hne1
    simpa using h
  -- numerator 2*arcsin
  have h_num : HasDerivAt (fun y => 2 * Real.arcsin y) (2 * (1 / Real.sqrt (1 - x ^ 2))) x := by
    have h := h_arcsin.const_mul 2
    simpa [mul_assoc] using h
  -- denominator s^3
  have h_den : HasDerivAt (fun y => (Real.sqrt (1 - y ^ 2)) ^ 3)
      (3 * (Real.sqrt (1 - x ^ 2)) ^ 2 * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2)))) x :=
    h_sqrt.pow 3
  have hne3 : (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := pow_ne_zero 3 hne_sqrt
  have h_term1 := h_num.div h_den hne3
  -- second term 2x/(1-x^2)
  have h_2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have h_u : HasDerivAt (fun y : ℝ => 1 - y ^ 2) (-2 * x) x := h_inner
  have h_term2 := h_2x.div h_u hne
  have hH1 : HasDerivAt H1fun
      ((2 * (1 / Real.sqrt (1 - x ^ 2)) * (Real.sqrt (1 - x ^ 2)) ^ 3
        - 2 * Real.arcsin x * (3 * (Real.sqrt (1 - x ^ 2)) ^ 2 * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2)))))
        / ((Real.sqrt (1 - x ^ 2)) ^ 3) ^ 2
      + (2 * (1 - x ^ 2) - 2 * x * (-2 * x)) / (1 - x ^ 2) ^ 2) x :=
    h_term1.add h_term2
  refine hH1.congr_deriv ?_
  simp only [H2fun]
  field_simp
  linear_combination (-2 * Real.sqrt (1 - x ^ 2) * ((1 - x ^ 2) + (Real.sqrt (1 - x ^ 2)) ^ 2)) * hsq

theorem ode_H (x : ℝ) (hx : |x| < 1) :
    (1 - x ^ 2) * H2fun x - 3 * x * H1fun x = 4 := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  simp only [H1fun, H2fun]
  have hs3 : (Real.sqrt (1 - x ^ 2)) ^ 3 ≠ 0 := pow_ne_zero 3 hne_sqrt
  have hs5 : (Real.sqrt (1 - x ^ 2)) ^ 5 ≠ 0 := pow_ne_zero 5 hne_sqrt
  have hsq2 : ((1:ℝ) - x ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hne
  field_simp [hs3, hs5, hsq2, hne, hne_sqrt]
  linear_combination (-6 * x * Real.arcsin x * (1 - x ^ 2)) * hsq

theorem Sfun_zero : Sfun 0 = 0 := by
  have h0 : Aterm 0 = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [Aterm, hn]
    · have h2n : 2 * n ≠ 0 := by omega
      simp [Aterm, zero_pow h2n]
  simp only [Sfun]
  rw [h0]
  exact tsum_zero

theorem Dfun_zero : Dfun 0 = 0 := by
  have h0 : Dterm 0 = fun _ => 0 := by
    funext n
    by_cases hn : n = 0
    · simp [Dterm, hn]
    · simp [Dterm, hn, zero_pow (by omega : 2 * n - 1 ≠ 0)]
  simp only [Dfun]
  rw [h0]
  exact tsum_zero

theorem Hfun_zero : Hfun 0 = 0 := by simp [Hfun, Real.arcsin_zero]

theorem H1fun_zero : H1fun 0 = 0 := by simp [H1fun, Real.arcsin_zero]

-- difference of derivatives satisfies homogeneous ODE
theorem hodeK (y : ℝ) (hy : |y| < 1) :
    (1 - y ^ 2) * (S2fun y - H2fun y) - 3 * y * (Dfun y - H1fun y) = 0 := by
  have h1 := ode_S y hy
  have h2 := ode_H y hy
  linear_combination h1 - h2

end MetaMathlibExt
