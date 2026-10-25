/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Def.StatisticalMechanics.Code.FK.TriHexCriticalReduction.Part2
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


theorem PeriodicGraph.wiredTwoPointProbability_nonneg
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    0 ≤ P.wiredTwoPointProbability p q x y := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem PeriodicGraph.wiredTwoPointProbability_le_one
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    P.wiredTwoPointProbability p q x y ≤ 1 := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num


end PeriodicPlanar
end FK
end StatMech
