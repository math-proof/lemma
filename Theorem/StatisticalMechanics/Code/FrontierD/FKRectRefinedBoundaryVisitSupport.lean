/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedBoundaryVisitSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedTranslatedLocalSupport
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialBoundaryPermutation.Part3
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedLocalDarts_map_eq_of_center_mod_eq
    {L : Nat} (pairing : Bool) (c z : Int × Int) (side : FKMedialSide)
    (h : (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    (fkRectRefinedLocalDarts pairing c side).map
        (fkRectIntegralSquareDartMod L) =
      (fkRectRefinedLocalDarts pairing z side).map
        (fkRectIntegralSquareDartMod L) := by
  have hx : ((c.1 : Int) : ZMod L) = ((z.1 : Int) : ZMod L) :=
    congrArg Prod.fst h
  have hy : ((c.2 : Int) : ZMod L) = ((z.2 : Int) : ZMod L) :=
    congrArg Prod.snd h
  have hxadd (k : Int) : (((c.1 + k : Int) : ZMod L)) =
      (((z.1 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hx
  have hyadd (k : Int) : (((c.2 + k : Int) : ZMod L)) =
      (((z.2 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hy
  cases pairing <;> cases side <;>
    simp [fkRectRefinedLocalDarts, fkRectRefinedDartPoint,
      fkRectRefinedSideOffset, fkRectIntegralSquareDartMod,
      Prod.ext_iff, hx, hy, hxadd, hyadd]

theorem fkRectRefinedPrimalCenterline_map_eq_of_center_mod_eq
    {L : Nat} (pairing : Bool) (c z : Int × Int)
    (h : (((c.1 : Int) : ZMod L), ((c.2 : Int) : ZMod L)) =
      (((z.1 : Int) : ZMod L), ((z.2 : Int) : ZMod L))) :
    (fkRectRefinedPrimalCenterlineDarts pairing c).map
        (fkRectIntegralSquareDartMod L) =
      (fkRectRefinedPrimalCenterlineDarts pairing z).map
        (fkRectIntegralSquareDartMod L) := by
  have hx : ((c.1 : Int) : ZMod L) = ((z.1 : Int) : ZMod L) :=
    congrArg Prod.fst h
  have hy : ((c.2 : Int) : ZMod L) = ((z.2 : Int) : ZMod L) :=
    congrArg Prod.snd h
  have hxadd (k : Int) : (((c.1 + k : Int) : ZMod L)) =
      (((z.1 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hx
  have hyadd (k : Int) : (((c.2 + k : Int) : ZMod L)) =
      (((z.2 + k : Int) : ZMod L)) := by
    push_cast
    exact congrArg (fun a : ZMod L => a + (k : ZMod L)) hy
  cases pairing <;>
    simp [fkRectRefinedPrimalCenterlineDarts,
      fkRectIntegralSquareDartMod, Prod.ext_iff, hx, hy, hxadd, hyadd]


theorem fkMedialDart_eq_west_or_east_of_vertex_eq_of_checkerColor
    {T : EvenTorus} (d : FKMedialDart T) (v : T.Vertex)
    (hvertex : d.1 = v)
    (hcolor : fkMedialCheckerColor d =
      fkMedialCheckerColor (fkMedialWestDart v)) :
    d = fkMedialWestDart v ∨ d = fkMedialEastDart v := by
  rcases d with ⟨w, side⟩
  change w = v at hvertex
  subst w
  cases side <;>
    simp [fkMedialWestDart, fkMedialEastDart,
      fkMedialCheckerColor, fkMedialSideVertical] at hcolor ⊢


theorem fkRectConfigurationOfEdges_pairing_eq_closed_or_open
    (R : FKRectTorus) (F : Finset R.EdgeIndex)
    (d : FKMedialDart R.medialTorus) :
    let f := fkRectTorusMedialEdgeEquiv R d.1
    fkRectConfigurationToMedialPairing R
        (fkRectConfigurationOfEdges R F) d.1 =
      if f ∈ F then !fkRectClosedPairingAtEdge f
      else fkRectClosedPairingAtEdge f := by
  classical
  simp [fkRectConfigurationToMedialPairing_apply,
    fkRectConfigurationOfEdges]
  split <;> rename_i h <;> simp [h]


theorem fkRectRefinedBondCenter_exists_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (u : Int × Int)
    (hcenter : c =
      ((fkRectRefinedBoundaryCanonicalCenter R d).1 +
          4 * (fkRectSquareDeckTranslation R u).1,
        (fkRectRefinedBoundaryCanonicalCenter R d).2 +
          4 * (fkRectSquareDeckTranslation R u).2)) :
    ∃ v : Int × Int,
      fkRectRefinedBondCenter c (fkMedialLocalMate pairing d).2 =
        ((fkRectRefinedBoundaryCanonicalCenter R
            (fkMedialBoundaryStep pairing d)).1 +
              4 * (fkRectSquareDeckTranslation R v).1,
          (fkRectRefinedBoundaryCanonicalCenter R
            (fkMedialBoundaryStep pairing d)).2 +
              4 * (fkRectSquareDeckTranslation R v).2) := by
  obtain ⟨v, hv⟩ :=
    fkRectRefinedBoundaryCenterAfter_exists_deck R pairing d 1
  simp only [fkRectRefinedBoundaryCenterAfter,
    Function.iterate_succ_apply, Function.iterate_zero_apply] at hv
  refine ⟨u + v, ?_⟩
  rw [hcenter]
  have hx := congrArg Prod.fst hv
  have hy := congrArg Prod.snd hv
  apply Prod.ext
  · simp [fkRectRefinedBondCenter, fkRectSquareDeckTranslation] at hx ⊢
    linear_combination hx
  · simp [fkRectRefinedBondCenter, fkRectSquareDeckTranslation] at hy ⊢
    linear_combination hy


end
end StatMech.FrontierD
