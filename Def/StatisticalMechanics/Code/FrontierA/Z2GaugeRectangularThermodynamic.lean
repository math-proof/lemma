/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeRectangularThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
open Filter Set Topology


namespace StatMech.FrontierA

noncomputable section

def cubicalRectangularWilsonFreeEnergy
    (beta : Real) (m n : Nat) : Real :=
  -Real.log
    (gaugeWilsonExpectation
      (cubicalPlaquetteIncidence (a := m) (b := n) (c := max m n))
      (fun _ : CubicalPlaquette m n (max m n) => beta)
      (cubicalXYLoop (a := m) (b := n) (c := max m n)
        (0 : Fin (max m n + 1))))


def cubicalRectangularDisorderFreeEnergy
    (beta : Real) (m n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := m) (b := n) (c := max m n))
    (fun _ : CubicalPlaquette m n (max m n) => gaugeDualCoupling beta)
    (cubicalXYSheet (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1)))


end
end StatMech.FrontierA
