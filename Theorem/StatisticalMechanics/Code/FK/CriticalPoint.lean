/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CriticalPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.FK.CriticalPoint
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


theorem fkTheta_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkTheta d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg


theorem fkTheta_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkTheta d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkTheta
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one


end FK
end StatMech
