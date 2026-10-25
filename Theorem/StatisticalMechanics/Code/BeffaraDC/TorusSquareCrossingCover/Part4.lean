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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part4
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


theorem torusPlanarHorizontalCrossing_imp_torus
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : HorizontalCrossing (torusPlanarPullback L omega)
      0 (n : ℤ) 0 (n : ℤ)) :
    torusSquareHorizontalCrossing L n omega := by
  obtain ⟨x, y, hxy⟩ := h
  have hxR : (x : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) := leftSide_subset x.2
  have hyR : (y : Site 2) ∈ rect 0 (n : ℤ) 0 (n : ℤ) := rightSide_subset y.2
  have hxS := torusReduceSite_mem_square L n hnL hxR
  have hyS := torusReduceSite_mem_square L n hnL hyR
  refine ⟨torusReduceSite L x, torusReduceSite L y, hxS, hyS, ?_, ?_, ?_⟩
  · obtain ⟨hx0, _⟩ := torusReduceSite_val_of_mem_rect L n hnL hxR
    rw [hx0, x.2.2]
    simp
  · obtain ⟨hy0, _⟩ := torusReduceSite_val_of_mem_rect L n hnL hyR
    rw [hy0, y.2.2]
    simp
  · exact hxy.map (torusPlanarSquarePrimalHom L n hnL omega)

theorem torus_not_horizontal_imp_planar_not_horizontal
    (L n : ℕ) [Fact (2 < L)] (hnL : n < L)
    (omega : TorusAmbientConfig L)
    (h : ¬ torusSquareHorizontalCrossing L n omega) :
    ¬ HorizontalCrossing (torusPlanarPullback L omega)
      0 (n : ℤ) 0 (n : ℤ) :=
  fun hp => h (torusPlanarHorizontalCrossing_imp_torus L n hnL omega hp)


end StatMech.BeffaraDC
