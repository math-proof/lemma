/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/LevyIsoperimetric.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace


@[expose] public noncomputable section

open MeasureTheory Metric Set

namespace LevyIsoperimetric

/-- The unit sphere $S^{n-1} \subseteq \mathbb{R}^n$, viewed as a subtype of
$\mathbb{R}^n$ consisting of vectors of norm $1$. -/
abbrev UnitSphere (n : ℕ) : Type :=
  ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)

end LevyIsoperimetric
end
