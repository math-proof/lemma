module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexFourByTwoOrientedNorthSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 0 1, (3 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 0 1) (3 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

def sixVertexFourByTwoOrientedEastSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 1 0, (3 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 1 0) (3 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

end StatMech.FrontierD
