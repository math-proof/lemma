/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part8
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKRectMergeInsertionOrder (R : FKRectTorus) :
    Finset R.EdgeIndex → List R.EdgeIndex → Prop
  | _, [] => True
  | F, e :: es =>
      e ∉ F ∧
        ¬ (fkMedialLoopGraph R.medialTorus
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))).Reachable
              (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
              (fkMedialEastDart (fkRectMedialVertexOfEdge R e)) ∧
        FKRectMergeInsertionOrder R (insert e F) es


end
end StatMech.FrontierD
