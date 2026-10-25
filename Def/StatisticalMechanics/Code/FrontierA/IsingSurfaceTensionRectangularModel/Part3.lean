/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionFeketeIdentification
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalGluing.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCriticalCoupling
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part2


namespace StatMech.FrontierA

noncomputable section

def finiteRectangularIsingDisorderFreeEnergy
    (J : Real) (m n : Nat) : Real :=
  multibondDisorderFreeEnergy
    (cubicalDualEnds (a := m) (b := n) (c := max m n))
    (fun _ : CubicalPlaquette m n (max m n) => J)
    (cubicalXYSheet (a := m) (b := n) (c := max m n)
      (0 : Fin (max m n + 1)))


def rectangularIsingDobrushinFreeEnergy
    (J : Real) (m n : Nat) : Real :=
  rectangularDobrushinFreeEnergy (gaugeCriticalCoupling J) m n


end
end StatMech.FrontierA
