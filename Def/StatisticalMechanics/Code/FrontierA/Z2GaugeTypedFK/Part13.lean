/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part10
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedFKTwoPoint (ends : P -> V × V) (rho : P -> Real)
    (x y : V) : Real :=
  typedFKEventMass ends rho (typedFKConnEvent ends x y)


def typedSpinProduct (sigma : V -> Bool) (x y : V) : Real :=
  if sigma x = sigma y then 1 else -1


def typedSpinXorEquiv (tau : V -> Bool) :
    (V -> Bool) ≃ (V -> Bool) where
  toFun sigma := typedSpinXor sigma tau
  invFun sigma := typedSpinXor sigma tau
  left_inv sigma := typedSpinXor_cancel_right sigma tau
  right_inv sigma := typedSpinXor_cancel_right sigma tau

end
end StatMech.FrontierA
