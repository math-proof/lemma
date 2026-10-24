/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/Wirtinger.lean -/


import sympy.atlas.Analysis.Calculus.Wirtinger
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

-- Applying Wirtinger's inequality to sine compares its square with its derivative's square.
example :
    intervalIntegral (fun x : ℝ => Real.sin x ^ 2) 0 Real.pi MeasureTheory.volume ≤
      intervalIntegral (fun x : ℝ => Real.cos x ^ 2) 0 Real.pi MeasureTheory.volume := by
  apply MetaMathlibExt.wirtinger_inequality Real.sin Real.cos
  · intro x _
    exact (Real.hasDerivAt_sin x).hasDerivWithinAt
  · exact Real.continuous_cos.continuousOn
  · simp
  · simp
