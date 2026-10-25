/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Def.StatisticalMechanics.Code.FrontierD.SixVertexAlignedFirstReturn.Part30
open StatMech.FrontierD


namespace StatMech.FrontierD

namespace FourByTwoPrefixBondAudit

theorem omega_ice : omega.IceRule := by decide

theorem eta_ice : eta.IceRule := by decide

theorem locallyDegreeTwo : SixVertexLocallyDegreeTwo omega eta := by decide

theorem cutVertex_alignedRetie_premises :
    let p := sixVertexLocalIncomingPattern omega cutVertex
    let q := sixVertexLocalIncomingPattern eta cutVertex
    p.Ice /\ q.Ice /\
      (sixVertexLocalDisagreementSides p q).card = 2 /\
      compatible true p /\ compatible true q /\
      p (0 : Fin 4) != q (0 : Fin 4) /\
      p (localMate true (localMate true (0 : Fin 4))) !=
        q (localMate true (localMate true (0 : Fin 4))) := by
  decide

theorem singletonPrefix_west_bond_failure :
    singletonPrefixPattern false cutVertex 0 =
      singletonPrefixPattern false
        (SixVertexArrows.cyclicPred
          sixVertexFourByTwoTorus.width_pos cutVertex.1, cutVertex.2) 1 := by
  decide

theorem singletonPrefix_not_bondConsistent :
    Not ((forall (layer : Bool)
        (v : sixVertexFourByTwoTorus.Vertex),
      singletonPrefixPattern layer v 0 =
        !singletonPrefixPattern layer
          (SixVertexArrows.cyclicPred
            sixVertexFourByTwoTorus.width_pos v.1, v.2) 1) /\
      (forall (layer : Bool)
        (v : sixVertexFourByTwoTorus.Vertex),
      singletonPrefixPattern layer v 2 =
        !singletonPrefixPattern layer
          (v.1, SixVertexArrows.cyclicPred
            sixVertexFourByTwoTorus.height_pos v.2) 3)) := by
  decide

end FourByTwoPrefixBondAudit
end StatMech.FrontierD
