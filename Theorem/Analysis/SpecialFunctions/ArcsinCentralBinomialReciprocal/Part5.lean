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
import Def.Analysis.SpecialFunctions.ArcsinCentralBinomialReciprocal.Part6


namespace MetaMathlibExt

theorem hasDerivAt_H (x : ℝ) (hx : |x| < 1) : HasDerivAt Hfun (H1fun x) x := by
  have hpos : (0:ℝ) < 1 - x ^ 2 := hpos_of_mem x hx
  have hne : (1:ℝ) - x ^ 2 ≠ 0 := ne_of_gt hpos
  have hne_sqrt : Real.sqrt (1 - x ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  obtain ⟨hne1, hnem1⟩ := hne_one_of_mem x hx
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
  have h_2x : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  have h_div := h_2x.div h_sqrt hne_sqrt
  have h_arcsin : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - x ^ 2)) x := by
    have h := Real.hasDerivAt_arcsin hnem1 hne1
    simpa using h
  have hH : HasDerivAt (fun y => (2 * y / Real.sqrt (1 - y ^ 2)) * Real.arcsin y)
      ((2 * Real.sqrt (1 - x ^ 2) - 2 * x * ((-2 * x) / (2 * Real.sqrt (1 - x ^ 2))))
        / (Real.sqrt (1 - x ^ 2)) ^ 2 * Real.arcsin x
        + (2 * x / Real.sqrt (1 - x ^ 2)) * (1 / Real.sqrt (1 - x ^ 2))) x :=
    h_div.mul h_arcsin
  have hHfun : (fun y => (2 * y / Real.sqrt (1 - y ^ 2)) * Real.arcsin y) = Hfun := by
    funext y
    simp [Hfun, mul_div_assoc]
  rw [hHfun] at hH
  refine hH.congr_deriv ?_
  simp only [H1fun]
  have hsq : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt (le_of_lt hpos)
  field_simp
  linear_combination (-x * Real.sqrt (1 - x ^ 2) + Real.arcsin x * (1 - x ^ 2)) * hsq

end MetaMathlibExt
