/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/SecantClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.PressureDiff
import Theorem.StatisticalMechanics.Code.FK.TiltSecant.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.SecantClose
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


def fsc_FreeEnergyData (d N : ℕ) (eb : Sym2 (boxVerts d N)) : Prop :=
  ∃ g : ℝ → ℝ, ConvexOn ℝ univ g
    ∧ (∀ t, wiredEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureRightDeriv g t)
    ∧ (∀ t, freeEdgeDensity d 2 (edgeIncl d N eb) (fsc_logistic t) = pressureLeftDeriv g t)


end FK
end StatMech
