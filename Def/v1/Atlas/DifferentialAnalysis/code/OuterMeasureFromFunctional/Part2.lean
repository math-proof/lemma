/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/OuterMeasureFromFunctional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Measure.Content
import Mathlib.MeasureTheory.OuterMeasure.Induced
import Mathlib.Topology.ContinuousMap.ZeroAtInfty
import Mathlib.Topology.Order
import Def.v1.Atlas.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.MeasuresAndSigmaAlgebras
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ContinuousFunctions
import Def.v1.Atlas.DifferentialAnalysis.code.ContinuousFunctions.Part2
import Theorem.v1.Atlas.DifferentialAnalysis.code.OuterMeasureFromFunctional


noncomputable section

open Set TopologicalSpace MeasureTheory

open scoped ENNReal NNReal Topology ZeroAtInfty

namespace MeasuresAndSigmaAlgebras

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X]

/-- Partition-of-unity inequality for the functional premeasure: if `f` is a compactly
supported test function with `0 ≤ f ≤ 1` whose support is covered by finitely many open sets
`U i`, then `u f ≤ ∑ i ∈ s, functionalMeasureOpen u (U i)`. -/
noncomputable def functionalOuterMeasure (u : C₀(X, ℝ) →L[ℝ] ℝ)
    (_ : IsPositiveLinearFunctional u) : OuterMeasure X :=
  inducedOuterMeasure
    (fun U (hU : IsOpen U) => functionalMeasureOpen u U hU)
    isOpen_empty
    (functionalMeasureOpen_empty u)

end MeasuresAndSigmaAlgebras
end
