/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/WeakConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
open MeasureTheory Filter Topology BoundedContinuousFunction
open scoped ENNReal NNReal


namespace StatMech

variable {E : Type*} [Countable E]


def WeakConvergesTo (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (ν : ProbabilityMeasure (ConfigSpace E)) : Prop :=
  Tendsto μ atTop (𝓝 ν)


end StatMech
