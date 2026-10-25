/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean -/

import Theorem.Analysis.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
import Lemma.Complex.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Measure.ResolventTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Analytic.IsolatedZeros
open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal


noncomputable section

def expPosWeight (t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-t) else 0

def expPosDensity (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (expPosWeight t)

def expPosMeasure : Measure ℝ :=
  volume.withDensity expPosDensity

end
