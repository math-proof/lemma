/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedPrimalEdgeDarts_eq_centerline
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedPrimalEdgeDarts R e =
      fkRectRefinedPrimalCenterlineDarts
        (fkRectClosedPairingAtEdge e)
        (fkRectRefinedPrimalEdgeCenter R e) := by
  have h := fkRectCanonicalSquareEdgeStep_eq R e
  by_cases hp : fkRectClosedPairingAtEdge e
  · simp [hp] at h
    unfold fkRectRefinedPrimalEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp, if_true]
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega
  · simp [hp] at h
    unfold fkRectRefinedPrimalEdgeDarts
      fkRectRefinedPrimalCenterlineDarts
    simp only [hp]
    unfold fkRectRefinedPrimalEdgeStart fkRectRefinedPrimalEdgeCenter
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [Prod.fst_sub, Prod.snd_sub] at h1 h2
    simp
    all_goals omega


theorem fkRectRefinedLocalDarts_west_interaction
    (pairing : Bool) (c : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing c .west).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L)) = 1 := by
  cases pairing
  · convert fkRectRefined_vertical_west_interaction
      (L := L) (c.1 : ZMod L) (c.2 : ZMod L) using 1 <;>
      simp [fkRectRefinedPrimalCenterlineDarts,
        fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] <;> ring
  · convert fkRectRefined_horizontal_west_interaction
      (L := L) (c.1 : ZMod L) (c.2 : ZMod L) using 1 <;>
      simp [fkRectRefinedPrimalCenterlineDarts,
        fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
        fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] <;> ring


theorem fkRectRefinedLocalDarts_east_interaction
    (pairing : Bool) (c : Int × Int) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts pairing c .east).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts pairing c).map
          (fkRectIntegralSquareDartMod L)) = -1 := by
  cases pairing
  · simpa [fkRectRefinedPrimalCenterlineDarts,
      fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] using
      fkRectRefined_vertical_east_interaction
        (L := L) (c.1 : ZMod L) (c.2 : ZMod L)
  · simpa [fkRectRefinedPrimalCenterlineDarts,
      fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod] using
      fkRectRefined_horizontal_east_interaction
        (L := L) (c.1 : ZMod L) (c.2 : ZMod L)


theorem fkRectRefinedPrimalEdge_west_interaction
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e)
          (fkRectRefinedPrimalEdgeCenter R e) .west).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) = 1 := by
  rw [fkRectRefinedPrimalEdgeDarts_eq_centerline]
  exact fkRectRefinedLocalDarts_west_interaction _ _


theorem fkRectRefinedPrimalEdge_east_interaction
    (R : FKRectTorus) (e : R.EdgeIndex) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (fkRectClosedPairingAtEdge e)
          (fkRectRefinedPrimalEdgeCenter R e) .east).map
            (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalEdgeDarts R e).map
          (fkRectIntegralSquareDartMod L)) = -1 := by
  rw [fkRectRefinedPrimalEdgeDarts_eq_centerline]
  exact fkRectRefinedLocalDarts_east_interaction _ _


theorem fkRectRefinedLocalDarts_open_interaction
    (closedPairing : Bool) (c : Int × Int) (side : FKMedialSide) :
    fkRectRefinedRawInteraction
        ((fkRectRefinedLocalDarts (!closedPairing) c side).map
          (fkRectIntegralSquareDartMod L))
        ((fkRectRefinedPrimalCenterlineDarts closedPairing c).map
          (fkRectIntegralSquareDartMod L)) = 0 := by
  cases closedPairing <;> cases side <;>
    simp [fkRectRefinedRawInteraction, fkRectRefinedLocalDarts,
      fkRectRefinedDartPoint, fkRectRefinedSideOffset,
      fkRectRefinedPrimalCenterlineDarts, fkRectIntegralSquareDartMod,
      dartHorizontal, dartVertical]


end
end StatMech.FrontierD
