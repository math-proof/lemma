/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectTorusSurfaceReduction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingRankTwoInsertion
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

def FKRectConnectedInsertionSurfaceBridge
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (r : (fkRectOpenGraph R
      (fkRectConfigurationOfEdges R F)).Walk
        (fkRectMedialWestPrimal R e) (fkRectMedialEastPrimal R e))
    (_heF : e ∉ F)
    (_hold : ¬ FKRectHasNet R (fkRectConfigurationOfEdges R F)) : Prop :=
  (¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e))) ↔
    ∃ q : (fkRectOpenGraph R
        (fkRectConfigurationOfEdges R F)).Walk
          (fkRectMedialWestPrimal R e) (fkRectMedialWestPrimal R e),
      FKRectWindingIndependent (fkRectWalkWinding R q)
        (fkRectWalkWinding R
          (fkRectInsertedFundamentalWalk R F e r))


end
end StatMech.FrontierD
