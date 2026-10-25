/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusCover.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleGeometry.Part5
import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part7
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem torusReduceSite_add_period_x
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![(L : ℤ), 0]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]

@[simp] theorem torusReduceSite_add_period_y
    (L : ℕ) [Fact (2 < L)] (z : Site 2) :
    torusReduceSite L (z + ![0, (L : ℤ)]) = torusReduceSite L z := by
  apply Prod.ext <;> simp [torusReduceSite]


theorem torusPlanarPullback_translate_period_x
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    translateConfig ![(L : ℤ), 0] (torusPlanarPullback L omega) =
      torusPlanarPullback L omega := by
  funext e
  unfold translateConfig torusPlanarPullback
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _
  exact torusReduceSite_add_period_x L z


theorem torusPlanarPullback_translate_period_y
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) :
    translateConfig ![0, (L : ℤ)] (torusPlanarPullback L omega) =
      torusPlanarPullback L omega := by
  funext e
  unfold translateConfig torusPlanarPullback
  rw [Sym2.map_map]
  congr 1
  apply Sym2.map_congr
  intro z _
  exact torusReduceSite_add_period_y L z


theorem torusPlanarPullback_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (torusPlanarPullback L) := by
  intro omega eta h
  funext e
  obtain ⟨c, rfl⟩ := torusEdgeOfCode_surjective L e
  rcases c with ⟨⟨x, y⟩, o⟩
  cases o with
  | horizontal =>
      have heq := congrFun h
        s(![(x.val : ℤ), (y.val : ℤ)],
          ![(x.val : ℤ) + 1, (y.val : ℤ)])
      rw [torusPlanarPullback_horizontal,
        torusPlanarPullback_horizontal] at heq
      simpa using heq
  | vertical =>
      have heq := congrFun h
        s(![(x.val : ℤ), (y.val : ℤ)],
          ![(x.val : ℤ), (y.val : ℤ) + 1])
      rw [torusPlanarPullback_vertical,
        torusPlanarPullback_vertical] at heq
      simpa using heq


end StatMech.BeffaraDC
