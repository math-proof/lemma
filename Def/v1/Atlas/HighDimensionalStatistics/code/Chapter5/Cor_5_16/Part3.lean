/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/HighDimensionalStatistics/code/Chapter5/Cor_5_16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Card
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.InfoTheory.Part3
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.InfoTheory
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_13
import Lemma.Measure.Atlas.v1.HighDimensionalStatistics.code.Chapter5.Cor_5_15
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_13.Part3
import Def.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_15
import Instance.v1.Atlas.HighDimensionalStatistics.code.Chapter5.Cor_5_16.Part2
open Real MeasureTheory InformationTheory


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
