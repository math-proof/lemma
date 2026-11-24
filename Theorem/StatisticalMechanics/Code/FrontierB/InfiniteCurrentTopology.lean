module
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Def.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology
open Filter MeasureTheory Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InfiniteCurrentTopology.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FrontierB

theorem continuous_restrictCurrent {E : Type*} (S : Finset E) :
    Continuous (restrictCurrent S : InfiniteCurrentConfig E → (↑S → ℕ)) :=
  continuous_pi fun e => continuous_apply e.1


end FrontierB
end StatMech
