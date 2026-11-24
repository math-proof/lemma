module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyObstruction.Part4
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoTwoCycleHall.Part7
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexHorizontalResidualCompletions.Part3
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexFourByTwoActiveKeyRepair.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFourByTwoActiveKeyRepair.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

noncomputable section

def sixVertexFourByTwoActiveCycleMiddleFirstConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoCycleMiddleFirst,
    sixVertexFourByTwoCycleMiddleFirst_ice,
    sixVertexFourByTwoCycleMiddleFirst_seamCount⟩

def sixVertexFourByTwoActiveCycleMiddleSecondConfiguration :
    SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
      sixVertexFourByTwoSectorOne :=
  ⟨sixVertexFourByTwoCycleMiddleSecond,
    sixVertexFourByTwoCycleMiddleSecond_ice,
    sixVertexFourByTwoCycleMiddleSecond_seamCount⟩


def sixVertexFourByTwoActiveCycleRepairPhysicalTarget :
    {pair : SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne ×
        SixVertexMarkedSectorConfiguration sixVertexFourByTwoTorus
          sixVertexFourByTwoSectorOne //
      sixVertexConfigurationPairBigrade pair =
        sixVertexFourByTwoActiveObstructionGrade} :=
  ⟨(sixVertexFourByTwoActiveCycleMiddleFirstConfiguration,
      sixVertexFourByTwoActiveCycleMiddleSecondConfiguration), by
    rw [sixVertexConfigurationPairBigrade_eq_horizontalPairBigrade]
    exact sixVertexFourByTwoActiveCycleRepair_bigrade⟩


end
end StatMech.FrontierD
