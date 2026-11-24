module
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedUnitPhysicalKey.Part14
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
public import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoSynchronizedPhysicalKeyCounterexample.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierD

def sixVertexFourByTwoOrientedSeed :
    SixVertexOrientedDisagreementDart sixVertexFourByTwoLowArrows
      sixVertexFourByTwoHighArrows :=
  ⟨⟨(sixVertexFourByTwoVertex 0 0, (1 : Fin 4)), by
      change sixVertexTorusEdgeDisagrees _ _
        (sixVertexTorusIncidentEdge sixVertexFourByTwoTorus
          (sixVertexFourByTwoVertex 0 0) (1 : Fin 4))
      rw [← sixVertexLocalIncomingPattern_ne_iff_edgeDisagrees]
      decide +revert⟩,
    by decide +revert⟩

noncomputable def sixVertexFourByTwoSynchronizedSeedComponent :=
  (sixVertexDegreeTwoSynchronizedGraph
    sixVertexFourByTwoLowArrows_ice sixVertexFourByTwoHighArrows_ice
    sixVertexFourByTwo_locallyDegreeTwo).connectedComponentMk
      sixVertexFourByTwoOrientedSeed

end StatMech.FrontierD
