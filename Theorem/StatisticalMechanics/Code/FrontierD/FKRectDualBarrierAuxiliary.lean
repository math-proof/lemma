/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectDualBarrierAuxiliary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSeamPatternPreservation.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierWindingMass.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectDualBarrierAuxiliary.Part2


namespace StatMech.FrontierD

noncomputable section

theorem fkRectColumnBand_connection_reachable_verticalCut
    (R : FKRectTorus) (left right lower upper : Nat)
    (hlower : 1 <= lower) (omega : R.Configuration)
    (x y : FKRectColumnBandVertex R left right lower upper)
    (hxy :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectColumnBandVertex R left right lower upper -> R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        FK.connEvent
          (fkRectInducedGraph R
            (fkRectColumnBand R left right lower upper)) x y) :
    (fkRectVerticalCutGraph R omega).Reachable x.1 y.1 := by
  let f :
      FK.openSub
          (fkRectInducedGraph R
            (fkRectColumnBand R left right lower upper))
          (FK.ocd_innerRestrict
            (Subtype.val :
              FKRectColumnBandVertex R left right lower upper -> R.Vertex)
            (fkRectFullGraphConfiguration R omega)) →g
        fkRectVerticalCutGraph R omega :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v huv
        rw [fkRectVerticalCutGraph, SimpleGraph.deleteEdges_adj]
        constructor
        · rw [← fkOpenSub_fullGraphConfiguration R omega]
          constructor
          · exact huv.1
          · simpa [FK.ocd_innerRestrict, FK.ocd_innerEdge_mk] using huv.2
        · intro hseam
          change fkRectCrossesVerticalSeam R s(u.1, v.1) at hseam
          rw [fkRectCrossesVerticalSeam_mk] at hseam
          rcases hseam with hseam | hseam
          · exact (Nat.ne_of_gt (Nat.zero_lt_one.trans_le
              (hlower.trans u.2.2.2.1))) hseam.1
          · exact (Nat.ne_of_gt (Nat.zero_lt_one.trans_le
              (hlower.trans v.2.2.2.1))) hseam.1 }
  exact hxy.map f


end
end StatMech.FrontierD
