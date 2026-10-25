/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectWiredDualBoundarySplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialToggleMerge.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Def.StatisticalMechanics.Code.FrontierD.FKRectWiredDualBoundarySplice.Part9
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryPerm_insert_merge_partition
    (R : FKRectTorus) (F : Finset R.EdgeIndex) (e : R.EdgeIndex)
    (heF : e ∉ F)
    (hmerge : ¬ (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable
          (fkMedialWestDart (fkRectMedialVertexOfEdge R e))
          (fkMedialEastDart (fkRectMedialVertexOfEdge R e)))
    (x : FKMedialBlackDart R.medialTorus) :
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R (insert e F)))).SameCycle
          (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ↔
      (fkMedialBlackBoundaryPerm
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))).SameCycle
            (fkMedialBlackDart0 (fkRectMedialVertexOfEdge R e)) x ∨
        (fkMedialBlackBoundaryPerm
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))).SameCycle
              (fkMedialBlackDart1 (fkRectMedialVertexOfEdge R e)) x := by
  rw [fkRectConfigurationToMedialPairing_insert R F e heF]
  exact fkMedialBlackBoundaryPerm_toggle_merge_partition
    (fkRectConfigurationToMedialPairing R
      (fkRectConfigurationOfEdges R F))
    (fkRectMedialVertexOfEdge R e) hmerge x


theorem fkRectBlackBoundaryPerm_sameCycle_insertEdgeList_of_mergeOrder
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex)
    (horder : FKRectMergeInsertionOrder R F es)
    {x y : FKMedialBlackDart R.medialTorus}
    (hxy : (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).SameCycle x y) :
    (fkMedialBlackBoundaryPerm
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R
          (fkRectInsertEdgeList R F es)))).SameCycle x y := by
  induction es generalizing F with
  | nil => simpa [fkRectInsertEdgeList]
  | cons e es ih =>
      rcases horder with ⟨heF, hmerge, htail⟩
      apply ih (insert e F) htail
      rw [fkRectConfigurationToMedialPairing_insert R F e heF]
      exact
        fkMedialBlackBoundaryPerm_toggle_sameCycle_mono_of_not_reachable
          (fkRectConfigurationToMedialPairing R
            (fkRectConfigurationOfEdges R F))
          (fkRectMedialVertexOfEdge R e) hmerge hxy


theorem fkRectMedialLoopGraph_reachable_insertEdgeList_of_mergeOrder
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (es : List R.EdgeIndex)
    (horder : FKRectMergeInsertionOrder R F es)
    {d e : FKMedialDart R.medialTorus}
    (hde : (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F))).Reachable d e) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R
          (fkRectInsertEdgeList R F es)))).Reachable d e := by
  induction es generalizing F with
  | nil => simpa [fkRectInsertEdgeList]
  | cons a es ih =>
      rcases horder with ⟨haF, hmerge, htail⟩
      apply ih (insert a F) htail
      rw [fkRectConfigurationToMedialPairing_insert R F a haF]
      exact fkMedialLoopGraph_toggle_reachable_mono_of_not_reachable
        (fkRectConfigurationToMedialPairing R
          (fkRectConfigurationOfEdges R F))
        (fkRectMedialVertexOfEdge R a) hmerge hde

end
end StatMech.FrontierD
