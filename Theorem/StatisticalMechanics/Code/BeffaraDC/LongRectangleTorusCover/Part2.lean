/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem bdcTorusVerticalWinding_projects_to_closed_torus
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    (h : bdcTorusVerticalWinding L omega) :
    ∃ x y : Site 2,
      Connected 2 (torusPlanarPullback L omega) x y ∧
      torusReduceSite L x = torusReduceSite L y ∧ x ≠ y := by
  obtain ⟨x, hx⟩ := h
  refine ⟨x, x + ![0, (L : ℤ)], hx, ?_, ?_⟩
  · exact (torusReduceSite_add_period_y L x).symm
  · intro heq
    have hcoord := congrFun heq 1
    simp at hcoord
    have hL : (0 : ℤ) < L := by
      exact_mod_cast (show 0 < L by have := (Fact.out : 2 < L); omega)
    omega


theorem torusSquareHorizontalCrossing_period_false
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    ¬ torusSquareHorizontalCrossing L L omega := by
  rintro ⟨x, y, hx, hy, hx0, hyL, hconn⟩
  have hlt := ZMod.val_lt y.1
  omega


theorem bdcTorusVerticalWinding_not_representable_by_periodSquare
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L)
    (_h : bdcTorusVerticalWinding L omega) :
    ¬ torusSquareHorizontalCrossing L L omega :=
  torusSquareHorizontalCrossing_period_false L omega


end StatMech.BeffaraDC
