/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoTwoCycleHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleObstructionRepair.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part5


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorZeroEquiv :
    Fin 4 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  Equiv.ofBijective sixVertexFourByTwoSectorZeroConfiguration
    ⟨sixVertexFourByTwoSectorZeroConfiguration_injective,
      sixVertexFourByTwoSectorZeroConfiguration_surjective⟩

def sixVertexFourByTwoSectorOneEquiv :
    Fin 28 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  Equiv.ofBijective sixVertexFourByTwoSectorOneConfiguration
    ⟨sixVertexFourByTwoSectorOneConfiguration_injective,
      sixVertexFourByTwoSectorOneConfiguration_surjective⟩

def sixVertexFourByTwoSectorTwoEquiv :
    Fin 50 ≃ SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  Equiv.ofBijective sixVertexFourByTwoSectorTwoConfiguration
    ⟨sixVertexFourByTwoSectorTwoConfiguration_injective,
      sixVertexFourByTwoSectorTwoConfiguration_surjective⟩

def sixVertexFourByTwoSourcePairEquiv :
    (Fin 4 × Fin 50) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorZero ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorTwo) :=
  Equiv.prodCongr sixVertexFourByTwoSectorZeroEquiv
    sixVertexFourByTwoSectorTwoEquiv

def sixVertexFourByTwoTargetPairEquiv :
    (Fin 28 × Fin 28) ≃
      (SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne) :=
  Equiv.prodCongr sixVertexFourByTwoSectorOneEquiv
    sixVertexFourByTwoSectorOneEquiv

end
end StatMech.FrontierD
