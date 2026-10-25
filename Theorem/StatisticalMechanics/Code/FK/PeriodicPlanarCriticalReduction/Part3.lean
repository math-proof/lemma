/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCriticalReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarThermodynamicDuality.Part2
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCriticalReduction.Part3
open MeasureTheory Set SimpleGraph


namespace StatMech

namespace FK

namespace PeriodicPlanar

open BeffaraDC

variable {V W : Type*} [DecidableEq V] [DecidableEq W]


section Countable

variable [Countable V]


theorem PeriodicGraph.wiredPercolationProbability_nonneg
    (P : PeriodicGraph V) (p q : ℝ) :
    0 ≤ P.wiredPercolationProbability p q := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem PeriodicGraph.wiredPercolationProbability_le_one
    (P : PeriodicGraph V) (p q : ℝ) :
    P.wiredPercolationProbability p q ≤ 1 := by
  unfold PeriodicGraph.wiredPercolationProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num


end Countable
end PeriodicPlanar
end FK
end StatMech
