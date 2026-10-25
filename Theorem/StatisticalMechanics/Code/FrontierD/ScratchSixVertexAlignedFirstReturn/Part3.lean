/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/ScratchSixVertexAlignedFirstReturn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialCheckerboard
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryToggleParity.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FiniteFirstReturn.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPairSwitchNoUnitCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierD.ScratchSixVertexAlignedFirstReturn.Part4
open StatMech.FrontierD


namespace ScratchLocalRetieC

theorem localIncomingPattern_arrowsOfIncomingPatterns
    {T : EvenTorus} (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
    (hwest : forall v,
      patterns v 0 =
        !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
    (hsouth : forall v,
      patterns v 2 =
        !patterns (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) 3)
    (v : T.Vertex) :
    sixVertexLocalIncomingPattern (arrowsOfIncomingPatterns patterns) v =
      patterns v := by
  funext d
  fin_cases d
  · simp [sixVertexLocalIncomingPattern, fkLoopWestIncoming,
      arrowsOfIncomingPatterns, hwest]
  · simp [sixVertexLocalIncomingPattern, fkLoopEastIncoming,
      arrowsOfIncomingPatterns]
  · simp [sixVertexLocalIncomingPattern, fkLoopSouthIncoming,
      arrowsOfIncomingPatterns, hsouth]
  · simp [sixVertexLocalIncomingPattern, fkLoopNorthIncoming,
      arrowsOfIncomingPatterns]

theorem arrowsOfIncomingPatterns_ice
    {T : EvenTorus} (patterns : T.Vertex -> SixVertexLocalIncomingPattern)
    (hwest : forall v,
      patterns v 0 =
        !patterns (SixVertexArrows.cyclicPred T.width_pos v.1, v.2) 1)
    (hsouth : forall v,
      patterns v 2 =
        !patterns (v.1,
          SixVertexArrows.cyclicPred T.height_pos v.2) 3)
    (hice : forall v, (patterns v).Ice) :
    (arrowsOfIncomingPatterns patterns).IceRule := by
  intro v
  rw [<- sixVertexLocalIncomingPattern_count]
  rw [localIncomingPattern_arrowsOfIncomingPatterns
    patterns hwest hsouth v]
  exact hice v

end ScratchLocalRetieC
