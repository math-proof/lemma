/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKInternalCylinder.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry.Part8
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKInternalCylinder.Part3
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

def cubicalInternalCentralInnerVertices (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  typedMarkedBondVertices
    (typedTrueEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m))
    (cubicalInternalCentralComplement N m hNm)

def cubicalInternalCentralUpperVertices (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  typedMarkedBondVertices
    (typedFalseEndpoint cubicalDualEnds
      (cubicalInternalCentralBlockSpin N m))
    (cubicalInternalCentralSheet N m hNm)


def cubicalInternalCentralUpperCoordinateVertices
    (N m : Nat) (hNm : N <= m) :
    Finset (CubicalDualVertex (oddCubeSide m) (oddCubeSide m) (oddCubeSide m)) :=
  (Finset.univ : Finset (Fin N × Fin N)).image fun ij =>
    some (CubicalCell.mk
      ⟨m + ij.1.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m + ij.2.val, by dsimp [oddCubeSide]; omega⟩
      ⟨m, by dsimp [oddCubeSide]; omega⟩)

end
end StatMech.FrontierA
