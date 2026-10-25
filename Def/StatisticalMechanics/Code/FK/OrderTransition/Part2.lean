/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/OrderTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FK.CriticalPoint.Part3
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.FK.DlrSandwich
import Theorem.StatisticalMechanics.Code.BeffaraDC.SelfDualValue
import Theorem.StatisticalMechanics.Code.FK.OrderTransition
open MeasureTheory
open scoped NNReal

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice StatMech.Percolation


def IsFirstOrderTransition (d : ℕ) {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) : Prop :=
  fkThetaFree d hp hp1 hq (q := q) = 0 ∧ 0 < fkTheta d hp hp1 hq (q := q)


end FK
end StatMech
