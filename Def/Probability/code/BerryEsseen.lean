/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/BerryEsseen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Finset

open scoped Real Topology NNReal ENNReal

/-- The density of the standard normal distribution:
`stdNormalDensity t = (2π)^{-1/2} exp(-t²/2)`. -/
noncomputable def stdNormalDensity (t : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(t ^ 2) / 2)

/-- The cumulative distribution function of the standard normal:
`Φ(x) = ∫_{-∞}^{x} (2π)^{-1/2} e^{-t²/2} dt`. -/
noncomputable def standardNormalCDF (x : ℝ) : ℝ :=
  ∫ t in Set.Iic x, stdNormalDensity t

end
