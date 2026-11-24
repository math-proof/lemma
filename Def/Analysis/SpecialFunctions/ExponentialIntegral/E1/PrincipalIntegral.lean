module
public import Theorem.Analysis.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
public import Theorem.Complex.SpecialFunctions.ExponentialIntegral.E1.EulerConstantNormalization
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.MeasureTheory.Measure.ResolventTransform
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Analytic.IsolatedZeros
open Filter Set Topology MeasureTheory
open scoped ENNReal NNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ExponentialIntegral/E1/PrincipalIntegral.lean -/
noncomputable section

def expPosWeight (t : ℝ) : ℝ :=
  if 0 < t then Real.exp (-t) else 0

def expPosDensity (t : ℝ) : ENNReal :=
  ENNReal.ofReal (expPosWeight t)

def expPosMeasure : Measure ℝ :=
  volume.withDensity expPosDensity

end
