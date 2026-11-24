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
public import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_16.Part2
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

/-- The minimax expected risk over the `ℓ¹`-ball `B₁(R)`: infimum over measurable estimators of
the worst-case expected squared error over `θ ∈ B₁(R)`. -/
noncomputable def minimaxExpRisk_l1 {d : ℕ}
    (P : (Fin d → ℝ) → Measure (Fin d → ℝ)) (R : ℝ) : ℝ :=
  ⨅ (θhat : MeasEstimator d),
    ⨆ θ ∈ l1Ball d R, ∫ Y, sqDist (θhat.1 Y) θ ∂(P θ)

open Classical in
/-- The constrained least squares estimator over the `ℓ¹`-ball `B₁(R)`; returns `0` if no
minimizer exists. -/
noncomputable def constrainedLSEstimator (d : ℕ) (R : ℝ) : Estimator' d :=
  fun Y => if h : ∃ θ ∈ l1Ball d R, ∀ θ' ∈ l1Ball d R, sqDist Y θ ≤ sqDist Y θ'
            then h.choose else fun _ => 0

/-- The trivial estimator `θ̂(Y) ≡ 0`. -/
def trivialEstimator (d : ℕ) : Estimator' d := fun _ => fun _ => 0

end MinimaxL1Ball
end
