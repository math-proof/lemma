/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPairUnionMatchingNoGo.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairTwoCycleCompletionHall.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairUnionMatchingNoGo


namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoSectorZero :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨0, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorOne :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨1, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoSectorTwo :
    Fin (sixVertexFourByTwoTorus.width + 1) :=
  ⟨2, by norm_num [sixVertexFourByTwoTorus]⟩

def sixVertexFourByTwoLowConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero :=
  ⟨sixVertexFourByTwoLowArrows,
    sixVertexFourByTwoLowArrows_ice,
    sixVertexFourByTwoLowArrows_seamCount⟩

def sixVertexFourByTwoHighConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorTwo :=
  ⟨sixVertexFourByTwoHighArrows,
    sixVertexFourByTwoHighArrows_ice,
    sixVertexFourByTwoHighArrows_seamCount⟩

def sixVertexFourByTwoSourceFineProfile :
    SixVertexHorizontalBoundedFineRowProfile sixVertexFourByTwoTorus :=
  sixVertexHorizontalPairBoundedFineRowProfile
    (sixVertexFourByTwoLowArrows.horizontal,
      sixVertexFourByTwoHighArrows.horizontal)

def sixVertexFourByTwoSourceFineProfilePair :
    SixVertexConfigurationPairFineProfileFiber sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorZero sixVertexFourByTwoSectorTwo
      sixVertexFourByTwoSourceFineProfile :=
  ⟨(sixVertexFourByTwoLowConfiguration,
      sixVertexFourByTwoHighConfiguration), rfl⟩


end
end StatMech.FrontierD
