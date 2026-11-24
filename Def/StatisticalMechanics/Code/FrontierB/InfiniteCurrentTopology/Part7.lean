module
public import Theorem.StatisticalMechanics.Code.Foundations.Ergodicity.Part2
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentTopology.Part6
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

def currentShift {E H : Type*} [Group H] [MulAction H E]
    (g : H) (n : InfiniteCurrentConfig E) : InfiniteCurrentConfig E :=
  fun e => n (g⁻¹ • e)

end FrontierB
end StatMech
