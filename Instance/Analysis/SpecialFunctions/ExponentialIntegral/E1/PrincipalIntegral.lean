/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean -/

import Theorem.Analysis.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
import Lemma.Complex.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Analytic.IsolatedZeros
import Def.Analysis.SpecialFunctions.ExponentialIntegral.E1.PrincipalIntegral
open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal


noncomputable section

instance : IsFiniteMeasure expPosMeasure := by
  unfold expPosMeasure expPosDensity
  exact isFiniteMeasure_withDensity_ofReal integrable_expPosWeight.hasFiniteIntegral

end
