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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


theorem torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : VerticalCrossing
      (fci_faceDualConfig (torusPlanarPullback L omega))
      0 (n : ℤ) 0 (n : ℤ)) :
    torusSquareHorizontalCrossing L n
      (torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)) := by
  obtain ⟨xb, yt, hconn⟩ := h
  have hxbR : (xb : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) :=
    bottomSide_subset xb.2
  have hytR : (yt : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) :=
    topSide_subset yt.2
  have hxbS := torusReduceSwapSite_mem_square L n hnL hxbR
  have hytS := torusReduceSwapSite_mem_square L n hnL hytR
  refine ⟨torusReduceSwapSite L xb, torusReduceSwapSite L yt,
    hxbS, hytS, ?_, ?_, ?_⟩
  · obtain ⟨_, hxb1⟩ := torusReduceSite_val_of_mem_rect L n hnL hxbR
    change ((((xb : Site 2) 1 : ℤ) : ZMod L)).val = 0
    change ((((xb : Site 2) 1 : ℤ) : ZMod L)).val =
      Int.toNat ((xb : Site 2) 1) at hxb1
    rw [hxb1, xb.2.2]
    simp
  · obtain ⟨_, hyt1⟩ := torusReduceSite_val_of_mem_rect L n hnL hytR
    change ((((yt : Site 2) 1 : ℤ) : ZMod L)).val = n
    change ((((yt : Site 2) 1 : ℤ) : ZMod L)).val =
      Int.toNat ((yt : Site 2) 1) at hyt1
    rw [hyt1, yt.2.2]
    simp
  · exact hconn.map (torusPlanarSquareFaceDualHom L n hnL omega)


theorem torus_concreteSquareCrossing_dual_cover
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (hn : 1 ≤ n) (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (hno : ¬ torusSquareHorizontalCrossing L n omega) :
    torusCellDualAmbientConfig L omega ∈
      torusSquareVerticalCrossingEvent L n := by
  rw [mem_torusSquareVerticalCrossingEvent]
  let eta := torusPlanarPullback L omega
  have hnoPlanar : ¬ HorizontalCrossing eta 0 (n : ℤ) 0 (n : ℤ) := by
    exact torus_not_horizontal_imp_planar_not_horizontal L n hnL omega hno
  have hband : VerticalCrossing (fci_faceDualConfig eta)
      0 ((n : ℤ) - 1) (-1) (n : ℤ) := by
    exact crr_square_compl_subset_faceDualRect_unconditional (n : ℤ)
      (by omega) hnoPlanar
  have hsquare : VerticalCrossing (fci_faceDualConfig eta)
      0 (n : ℤ) 0 (n : ℤ) :=
    torus_faceBand_verticalCrossing_to_square (by omega) hband
  exact torusPlanarFaceVerticalCrossing_imp_rotatedTorusHorizontal
    L n hnL omega hsquare


theorem torus_concreteSquareCrossing_ge_one_div_one_add_q_unconditional
    (L : ℕ) [Fact (2 < L)] (n : ℕ) (hn : 1 ≤ n) (hnL : n < L)
    {q : ℝ} (hq1 : 1 ≤ q) :
    1 / (1 + q) ≤
      torusAmbientEventProbability L (selfDualPoint q) q
        (torusSquareHorizontalCrossingEvent L n) := by
  apply torus_concreteSquareCrossing_ge_one_div_one_add_q_of_cover
    L n hn hnL hq1
  intro omega hno
  exact torus_concreteSquareCrossing_dual_cover L n hn hnL omega hno

end StatMech.BeffaraDC
