/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusWindingEvent.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRightBand_chain_reachable_verticalCut
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t) :
    (fkRectVerticalCutGraph R omega).Reachable
      (fkRectRowOneVertex R x) (fkRectLastRowVertex R x) := by
  apply fkRectRightStripBand_connection_reachable_verticalCut
    R cut 1 (R.height - 1) (by omega) omega
      (fkRectRightBandRowOne R cut x hx)
      (fkRectRightBandLastRow R cut x hx)
  exact hchain _ hpair


theorem fkRectVerticalWindingEvent_of_rightBand_chain
    (R : FKRectTorus) (cut : Nat) (x : Fin R.width)
    (hx : cut ≤ x.val) (omega : R.Configuration)
    (t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) ×
      FKRectRightStripBandVertex R cut 1 (R.height - 1)))
    (hpair : (fkRectRightBandRowOne R cut x hx,
      fkRectRightBandLastRow R cut x hx) ∈ t)
    (hchain :
      FK.ocd_innerRestrict
          (Subtype.val :
            FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex)
          (fkRectFullGraphConfiguration R omega) ∈
        fkRectInducedConnectionChainEvent R
          (fkRectRightStripBand R cut 1 (R.height - 1)) t)
    (hseam : omega (fkRectVerticalSeamEdgeAt R x) = true)
    (hattach : omega (fkRectRowZeroAttachmentEdgeAt R x) = true) :
    omega ∈ fkRectVerticalWindingEvent R := by
  let v0 := fkRectRowZeroVertex R x
  let v1 := fkRectRowOneVertex R x
  let vt := fkRectLastRowVertex R x
  have hseamAdj : (fkRectOpenGraph R omega).Adj v0 vt := by
    refine ⟨fkRectVerticalSeamEdgeAt R x, hseam, ?_⟩
    exact fkRectVerticalSeamEdgeAt_indexedEdge R x
  have hattachAdj : (fkRectVerticalCutGraph R omega).Adj v0 v1 := by
    rw [fkRectVerticalCutGraph, SimpleGraph.deleteEdges_adj]
    constructor
    · refine ⟨fkRectRowZeroAttachmentEdgeAt R x, hattach, ?_⟩
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      exact Sym2.eq_swap
    · intro hcross
      apply fkRectRowZeroAttachmentEdgeAt_not_crosses R x
      rw [fkRectRowZeroAttachmentEdgeAt_indexedEdge]
      simpa only [Sym2.eq_swap] using hcross
  have hband : (fkRectVerticalCutGraph R omega).Reachable v1 vt := by
    exact fkRectRightBand_chain_reachable_verticalCut
      R cut x hx omega t hpair hchain
  refine ⟨v0, vt, hseamAdj, ?_, hattachAdj.reachable.trans hband⟩
  rw [← fkRectVerticalSeamEdgeAt_indexedEdge R x]
  exact fkRectVerticalSeamEdgeAt_crosses R x

end
end StatMech.FrontierD
