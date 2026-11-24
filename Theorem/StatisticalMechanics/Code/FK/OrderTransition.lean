module
public import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
public import Theorem.StatisticalMechanics.Code.FK.IvProperties
public import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
public import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
public import Def.StatisticalMechanics.Code.FK.OrderTransition
open MeasureTheory
open scoped NNReal
set_option linter.unusedSectionVars false


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


theorem fkThetaFree_nonneg (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    0 ≤ fkThetaFree d hp hp1 hq (q := q) :=
  ENNReal.toReal_nonneg


theorem fkThetaFree_le_one (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    fkThetaFree d hp hp1 hq (q := q) ≤ 1 := by
  unfold fkThetaFree
  rw [Measure.real]
  refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
  rw [ENNReal.ofReal_one]
  exact prob_le_one


end FK
end StatMech
