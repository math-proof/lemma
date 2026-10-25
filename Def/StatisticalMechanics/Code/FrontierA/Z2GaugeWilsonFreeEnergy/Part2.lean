/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonSupport
import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy
open scoped BigOperators symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def multibondIsingAction (ends : P → V × V) (J : P → Real)
    (s : V → Bool) : Real :=
  ∑ p : P, J p * if s (ends p).1 = s (ends p).2 then 1 else -1


end
end StatMech.FrontierA
