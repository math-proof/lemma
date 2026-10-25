/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceSeamWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamBarrier.Part4
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRankOneWindingTail
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectAugmentedBarrierPatternCost
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectCutMedialColumn_canonicalVerticalSeamSign_add
    (R : FKRectTorus) (x : Fin R.width) :
    fkMedialCanonicalVerticalSeamSign R.medialTorus
        (fkRectCutMedialColumn R x false) +
      fkMedialCanonicalVerticalSeamSign R.medialTorus
        (fkRectCutMedialColumn R x true) = 0 := by
  unfold fkMedialCanonicalVerticalSeamSign fkMedialCheckerColor
    fkMedialVertexParity fkMedialVerticalSeamDart fkMedialSideVertical
  have heven : Even (2 * x.val) := even_two.mul_right x.val
  have hodd : ¬ Even (1 + 2 * x.val) := by
    rw [Nat.even_add]
    simp [heven]
  by_cases hrow : Even (svFinLast R.medialTorus.height_pos).val
  · simp [hrow, heven, hodd, fkRectCutMedialColumn_val]
  · simp [hrow, heven, hodd, fkRectCutMedialColumn_val]


theorem fkRectCutMedialColumns_reachable_of_both_open
    (R : FKRectTorus) (omega : R.Configuration) (x : Fin R.width)
    (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
    (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
    (fkMedialLoopGraph R.medialTorus
      (fkRectConfigurationToMedialPairing R omega)).Reachable
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x false))
        (fkMedialVerticalSeamDart R.medialTorus
          (fkRectCutMedialColumn R x true)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let i0 := fkRectCutMedialColumn R x false
  let i1 := fkRectCutMedialColumn R x true
  let top0 := fkMedialVerticalSeamDart R.medialTorus i0
  let bot0 : FKMedialDart R.medialTorus :=
    ((i0, ⟨0, R.height_pos⟩), .south)
  let east0 : FKMedialDart R.medialTorus :=
    ((i0, ⟨0, R.height_pos⟩), .east)
  let west1 : FKMedialDart R.medialTorus :=
    ((i1, ⟨0, R.height_pos⟩), .west)
  let bot1 : FKMedialDart R.medialTorus :=
    ((i1, ⟨0, R.height_pos⟩), .south)
  let top1 := fkMedialVerticalSeamDart R.medialTorus i1
  have hi : finitePeriodicSucc R.medialTorus.width_pos i0 = i1 := by
    exact fkRectCutMedialColumn_false_succ R x
  have hv0 : fkRectTorusMedialEdgeEquiv R (i0, ⟨0, R.height_pos⟩) =
      (false, (x, ⟨0, R.height_pos⟩)) := by
    rw [show (i0, ⟨0, R.height_pos⟩) = fkRectMedialVertexOfEdge R
        (false, (x, ⟨0, R.height_pos⟩)) by
      apply Prod.ext
      · rfl
      · apply Fin.ext; rfl]
    exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _
  have hv1 : fkRectTorusMedialEdgeEquiv R (i1, ⟨0, R.height_pos⟩) =
      (true, (x, ⟨0, R.height_pos⟩)) := by
    rw [show (i1, ⟨0, R.height_pos⟩) = fkRectMedialVertexOfEdge R
        (true, (x, ⟨0, R.height_pos⟩)) by
      apply Prod.ext
      · rfl
      · apply Fin.ext; rfl]
    exact fkRectTorusMedialEdgeEquiv_vertexOfEdge R _
  have hp0 : pairing (i0, ⟨0, R.height_pos⟩) = false := by
    simp [pairing, fkRectConfigurationToMedialPairing_apply, hv0,
      hfalse, fkRectClosedPairingAtEdge]
  have hp1 : pairing (i1, ⟨0, R.height_pos⟩) = true := by
    simp [pairing, fkRectConfigurationToMedialPairing_apply, hv1,
      htrue, fkRectClosedPairingAtEdge]
  have h01 : (fkMedialLoopGraph R.medialTorus pairing).Adj top0 bot0 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [top0, bot0, fkMedialVerticalSeamDart, fkMedialBondMate,
      finitePeriodicSucc_svFinLast]
  have h12 : (fkMedialLoopGraph R.medialTorus pairing).Adj bot0 east0 := by
    rw [fkMedialLoopGraph_adj_iff]
    left
    simp [bot0, east0, fkMedialLocalMate, hp0]
  have h23 : (fkMedialLoopGraph R.medialTorus pairing).Adj east0 west1 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [east0, west1, fkMedialBondMate, hi]
  have h34 : (fkMedialLoopGraph R.medialTorus pairing).Adj west1 bot1 := by
    rw [fkMedialLoopGraph_adj_iff]
    left
    simp [west1, bot1, fkMedialLocalMate, hp1]
  have h45 : (fkMedialLoopGraph R.medialTorus pairing).Adj bot1 top1 := by
    rw [fkMedialLoopGraph_adj_iff]
    right
    simp [top1, bot1, fkMedialVerticalSeamDart, fkMedialBondMate,
      SixVertexArrows.cyclicPred, svFinLast]
  exact h01.reachable.trans <| h12.reachable.trans <|
    h23.reachable.trans <| h34.reachable.trans h45.reachable


theorem fkRectCutMedialColumns_component_eq_of_both_open
    (R : FKRectTorus) (omega : R.Configuration) (x : Fin R.width)
    (hfalse : omega (false, (x, ⟨0, R.height_pos⟩)) = true)
    (htrue : omega (true, (x, ⟨0, R.height_pos⟩)) = true) :
    (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x false)) =
      (fkMedialLoopGraph R.medialTorus
        (fkRectConfigurationToMedialPairing R omega)).connectedComponentMk
          (fkMedialVerticalSeamDart R.medialTorus
            (fkRectCutMedialColumn R x true)) := by
  exact ConnectedComponent.sound
    (fkRectCutMedialColumns_reachable_of_both_open
      R omega x hfalse htrue)


end
end StatMech.FrontierD
