module
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Card
public import Mathlib.Topology.MetricSpace.Bounded
public import Mathlib.Topology.Sequences
public import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_13
public import Theorem.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_15
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13.Part3
public import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_15
open Real MeasureTheory InformationTheory


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace MinimaxL1Ball

/-- The `ℓ¹`-norm `|θ|_1 = ∑_i |θ_i|`. -/
def l1norm {d : ℕ} (θ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, |θ i|

/-- The `ℓ¹`-ball of radius `R`: vectors with `|θ|_1 ≤ R`. -/
def l1Ball (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) :=
  {θ | l1norm θ ≤ R}

/-- Squared Euclidean distance between two vectors in `ℝ^d`. -/
def sqDist {d : ℕ} (θ₁ θ₂ : Fin d → ℝ) : ℝ :=
  ∑ i : Fin d, (θ₁ i - θ₂ i) ^ 2

/-- A (not-necessarily measurable) estimator `ℝ^d → ℝ^d`. -/
def Estimator' (d : ℕ) := (Fin d → ℝ) → (Fin d → ℝ)

end MinimaxL1Ball
end
