/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic
open Filter Topology Set
open scoped BigOperators Topology


namespace StatMech.FrontierA

noncomputable section

def cubicalSquareWilsonFreeEnergy (beta : Real) (n : Nat) : Real :=
  -Real.log
    (gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := n + 1) (b := n + 1) (c := n + 1))
      (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) => beta)
      (cubicalXYLoop (a := n + 1) (b := n + 1) (c := n + 1)
        (0 : Fin (n + 1 + 1))))


def cubicalSquareDisorderFreeEnergy (beta : Real) (n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := n + 1) (b := n + 1) (c := n + 1))
    (fun _ : CubicalPlaquette (n + 1) (n + 1) (n + 1) =>
      gaugeDualCoupling beta)
    (cubicalXYSheet (a := n + 1) (b := n + 1) (c := n + 1)
      (0 : Fin (n + 1 + 1)))


end
end StatMech.FrontierA
