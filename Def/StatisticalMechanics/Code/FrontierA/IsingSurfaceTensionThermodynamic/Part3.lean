/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part2
open Filter Topology Set
open scoped BigOperators Topology


namespace StatMech.FrontierA

noncomputable section

def cubicalSquareWilsonDensity (beta : Real) (n : Nat) : Real :=
  cubicalSquareWilsonFreeEnergy beta n / ((n + 1 : Nat) : Real) ^ 2


def cubicalSquareDisorderDensity (beta : Real) (n : Nat) : Real :=
  cubicalSquareDisorderFreeEnergy beta n / ((n + 1 : Nat) : Real) ^ 2


end
end StatMech.FrontierA
