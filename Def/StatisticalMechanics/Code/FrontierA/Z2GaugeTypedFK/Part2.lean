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
import Instance.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedESEdgeFactor (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (p : P) (b : Bool) : Real :=
  if b then
    rho p * if sigma (ends p).1 = sigma (ends p).2 <-> p ∉ D then 1 else 0
  else 1 - rho p


def typedESWeight (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) (sigma : V -> Bool) (omega : P -> Bool) : Real :=
  ∏ p : P, typedESEdgeFactor ends rho D sigma p (omega p)


def typedESZ (ends : P -> V × V) (rho : P -> Real)
    (D : Finset P) : Real :=
  ∑ omega : P -> Bool, ∑ sigma : V -> Bool,
    typedESWeight ends rho D sigma omega

end
end StatMech.FrontierA
