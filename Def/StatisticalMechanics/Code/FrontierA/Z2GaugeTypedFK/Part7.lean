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
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part5
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def typedFKWeight (ends : P -> V × V) (rho : P -> Real)
    (omega : P -> Bool) : Real :=
  ∑ sigma : V -> Bool, typedESWeight ends rho ∅ sigma omega

def typedFKZ (ends : P -> V × V) (rho : P -> Real) : Real :=
  ∑ omega : P -> Bool, typedFKWeight ends rho omega

def typedFKProb (ends : P -> V × V) (rho : P -> Real)
    (omega : P -> Bool) : Real :=
  typedFKWeight ends rho omega / typedFKZ ends rho

def typedFKEventMass (ends : P -> V × V) (rho : P -> Real)
    (A : Set (P -> Bool)) : Real :=
  ∑ omega : P -> Bool,
    typedFKProb ends rho omega * A.indicator (fun _ => (1 : Real)) omega

end
end StatMech.FrontierA
