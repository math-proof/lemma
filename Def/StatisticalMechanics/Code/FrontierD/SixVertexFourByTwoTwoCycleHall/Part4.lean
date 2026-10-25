/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part3


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorZeroConfiguration (i : Fin 4) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  ⟨sixVertexFourByTwoSectorZeroArrows i,
    (sixVertexFourByTwoSectorZeroArrows_valid i).1,
    (sixVertexFourByTwoSectorZeroArrows_valid i).2⟩

def sixVertexFourByTwoSectorOneConfiguration (i : Fin 28) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoSectorOneArrows i,
    (sixVertexFourByTwoSectorOneArrows_valid i).1,
    (sixVertexFourByTwoSectorOneArrows_valid i).2⟩

def sixVertexFourByTwoSectorTwoConfiguration (i : Fin 50) :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  ⟨sixVertexFourByTwoSectorTwoArrows i,
    (sixVertexFourByTwoSectorTwoArrows_valid i).1,
    (sixVertexFourByTwoSectorTwoArrows_valid i).2⟩

def sixVertexFourByTwoHorizontalMask
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Nat :=
  Nat.ofBits fun i : Fin 8 =>
    let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
    omega.horizontal (yx.2, yx.1)

def sixVertexFourByTwoVerticalMask
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Nat :=
  Nat.ofBits fun i : Fin 8 =>
    let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
    omega.vertical (yx.2, yx.1)

def sixVertexFourByTwoHorizontalMaskFin
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Fin 256 :=
  ⟨sixVertexFourByTwoHorizontalMask omega, by
    simpa [sixVertexFourByTwoHorizontalMask] using
      Nat.ofBits_lt_two_pow (fun i : Fin 8 =>
        let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
        omega.horizontal (yx.2, yx.1))⟩

def sixVertexFourByTwoVerticalMaskFin
    (omega : SixVertexArrows sixVertexFourByTwoTorus) : Fin 256 :=
  ⟨sixVertexFourByTwoVerticalMask omega, by
    simpa [sixVertexFourByTwoVerticalMask] using
      Nat.ofBits_lt_two_pow (fun i : Fin 8 =>
        let yx := (finProdFinEquiv (m := 2) (n := 4)).symm i
        omega.vertical (yx.2, yx.1))⟩

end
end StatMech.FrontierD
