/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossingCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCounterexample
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


noncomputable def torusPlanarFaceDualHom
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    openSubgraph 2 (fci_faceDualConfig (torusPlanarPullback L omega)) →g
      FK.openSub (onsTorusGraph L)
        (torusAmbientConfigExtend L
          (torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega))) where
  toFun := torusReduceSwapSite L
  map_rel' := by
    intro f g hfg
    rw [FK.openSub_adj]
    refine ⟨torusReduceSwapSite_adj L hfg.1, ?_⟩
    have hf : f = ![f 0, f 1] := by
      funext i
      fin_cases i <;> simp
    rw [hf] at hfg ⊢
    rcases crr_face_nbr_cases (f 0) (f 1) g hfg.1 with hg | hg | hg | hg <;>
      subst g
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_right] at hopen
      simp only [faceCorner10, faceCorner11] at hopen
      rw [torusPlanarPullback_vertical] at hopen
      have hclosed : omega
          (torusVerticalEdge L ((f 0 + 1 : ℤ) : ZMod L) ((f 1 : ℤ) : ZMod L)) =
          false := by simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0 + 1, f 1]) =
          (torusVerticalEdge L ((f 1 : ℤ) : ZMod L) ((f 0 : ℤ) : ZMod L) :
            Sym2 (ZMod L × ZMod L)) := by
        simp [torusReduceSwapSite, torusVerticalEdge_val]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusVerticalEdge L _ _).2,
        torusAmbientSwapCellDual_vertical]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_left] at hopen
      simp only [faceCorner00, faceCorner01] at hopen
      rw [torusPlanarPullback_vertical] at hopen
      have hclosed : omega
          (torusVerticalEdge L ((f 0 : ℤ) : ZMod L) ((f 1 : ℤ) : ZMod L)) =
          false := by simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0 - 1, f 1]) =
          (torusVerticalEdge L ((f 1 : ℤ) : ZMod L)
            (((f 0 - 1 : ℤ) : ZMod L)) : Sym2 (ZMod L × ZMod L)) := by
        rw [torusVerticalEdge_orientation_independent]
        simp [torusReduceSwapSite]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusVerticalEdge L _ _).2,
        torusAmbientSwapCellDual_vertical]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_top] at hopen
      simp only [faceCorner01, faceCorner11] at hopen
      rw [torusPlanarPullback_horizontal] at hopen
      have hclosed : omega
          (torusHorizontalEdge L ((f 0 : ℤ) : ZMod L)
            ((f 1 + 1 : ℤ) : ZMod L)) = false := by
        simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0, f 1 + 1]) =
          (torusHorizontalEdge L ((f 1 : ℤ) : ZMod L)
            ((f 0 : ℤ) : ZMod L) : Sym2 (ZMod L × ZMod L)) := by
        simp [torusReduceSwapSite, torusHorizontalEdge_val]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusHorizontalEdge L _ _).2,
        torusAmbientSwapCellDual_horizontal]
      simpa using hclosed
    · have hopen := hfg.2
      rw [fci_faceDualConfig, fci_faceEdgeEquiv_mk_of_adj hfg.1,
        sharedPrimalEdge_bottom] at hopen
      simp only [faceCorner00, faceCorner10] at hopen
      rw [torusPlanarPullback_horizontal] at hopen
      have hclosed : omega
          (torusHorizontalEdge L ((f 0 : ℤ) : ZMod L)
            ((f 1 : ℤ) : ZMod L)) = false := by
        simpa only [Bool.not_eq_true'] using hopen
      have he : s(torusReduceSwapSite L ![f 0, f 1],
          torusReduceSwapSite L ![f 0, f 1 - 1]) =
          (torusHorizontalEdge L (((f 1 - 1 : ℤ) : ZMod L))
            ((f 0 : ℤ) : ZMod L) : Sym2 (ZMod L × ZMod L)) := by
        rw [torusHorizontalEdge_orientation_independent]
        simp [torusReduceSwapSite]
      rw [he, torusAmbientConfigExtend,
        dif_pos (torusHorizontalEdge L _ _).2,
        torusAmbientSwapCellDual_horizontal]
      simpa using hclosed


end StatMech.BeffaraDC
