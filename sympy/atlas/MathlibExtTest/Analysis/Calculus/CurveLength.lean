/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/CurveLength.lean -/


import sympy.atlas.Analysis.Calculus.CurveLength
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul

open MeasureTheory Set

-- The within-derivative formula computes the variation of the identity segment.
example : eVariationOn (fun t : ℝ => t) (Icc 0 1) = 1 := by
  rw [ContDiffOn.eVariationOn_Icc_eq_ofReal_integral_norm_derivWithin
    (γ := fun t : ℝ => t) (by norm_num) contDiff_id.contDiffOn]
  rw [← intervalIntegral.integral_norm_deriv_eq_integral_norm_derivWithin_Icc
    (fun t : ℝ => t) (by norm_num)]
  simp

-- A straight segment has variation equal to the norm of its displacement.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (v : E) :
    eVariationOn (fun t : ℝ => t • v) (Icc 0 1) = ENNReal.ofReal ‖v‖ := by
  rw [MetaMathlibExt.curve_length_eq_integral_norm_deriv
    (γ := fun t : ℝ => t • v) (by norm_num) (contDiff_smul_const v).contDiffOn]
  have hderiv (t : ℝ) : deriv (fun s : ℝ => s • v) t = v := by
    simpa using ((hasDerivAt_id t).smul_const v).deriv
  simp_rw [hderiv]
  simp
