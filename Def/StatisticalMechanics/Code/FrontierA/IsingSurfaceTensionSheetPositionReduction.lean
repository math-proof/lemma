/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetPositionReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionMeanfieldLower
open Filter Set Topology


namespace StatMech.FrontierA

noncomputable section

def oddCubicalLowerSheetFreeEnergy (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta)
    (cubicalXYSheet (a := L) (b := L) (c := L) (0 : Fin (L + 1)))


def oddCubicalCentralSheetFreeEnergy (beta : Real) (n : Nat) : Real :=
  let L := 2 * n + 1
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := L) (b := L) (c := L))
    (fun _ : CubicalPlaquette L L L => beta)
    (cubicalXYSheet (a := L) (b := L) (c := L)
      (⟨n + 1, by omega⟩ : Fin (L + 1)))

end
end StatMech.FrontierA
