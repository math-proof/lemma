/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeDisorderGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeDisorderGluing
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.flexible false
set_option linter.style.multiGoal false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def eraseMultibondCouplings (J : P → Real) (S : Finset P) : P → Real :=
  fun p => if p ∈ S then 0 else J p


end
end StatMech.FrontierA
