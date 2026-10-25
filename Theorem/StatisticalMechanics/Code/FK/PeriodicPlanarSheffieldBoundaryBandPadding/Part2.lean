/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldBoundaryBandPadding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldDeepTemplateGridAssembly
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldOrientedBoundary
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldBoundaryBandPadding
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem le_commonPrimalDualBandHalfWidth
    (primalLeft primalRight primalBottom primalTop
      dualLeft dualRight dualBottom dualTop : Nat) :
    let M := commonPrimalDualBandHalfWidth
      primalLeft primalRight primalBottom primalTop
      dualLeft dualRight dualBottom dualTop
    primalLeft ≤ M ∧ primalRight ≤ M ∧
    primalBottom ≤ M ∧ primalTop ≤ M ∧
    dualLeft ≤ M ∧ dualRight ≤ M ∧
    dualBottom ≤ M ∧ dualTop ≤ M := by
  simp [commonPrimalDualBandHalfWidth]


end StatMech.FK.PeriodicPlanar
