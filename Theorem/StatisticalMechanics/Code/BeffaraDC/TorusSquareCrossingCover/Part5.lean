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
import Def.StatisticalMechanics.Code.BeffaraDC.TorusSquareCrossingCover.Part5
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.RSW.Box

open StatMech.Universality


@[simp] theorem torusReduceSwapSite_mk (L : ℕ) (a b : ℤ) :
    torusReduceSwapSite L ![a, b] = ((b : ZMod L), (a : ZMod L)) := by
  rfl

theorem torusReduceSwapSite_adj (L : ℕ) [Fact (2 < L)] {x y : Site 2}
    (hxy : (hypercubicLattice 2).Adj x y) :
    (onsTorusGraph L).Adj (torusReduceSwapSite L x)
      (torusReduceSwapSite L y) := by
  simpa [torusReduceSwapSite, torusReduceSite, torusCoordSwap] using
    (onsTorusGraph_adj_coordSwap L (torusReduceSite L x)
      (torusReduceSite L y)).2 (torusReduceSite_adj L hxy)

theorem torusPlanarPullback_horizontal (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) (a b : ℤ) :
    torusPlanarPullback L omega s(![a, b], ![a + 1, b]) =
      omega (torusHorizontalEdge L (a : ZMod L) (b : ZMod L)) := by
  unfold torusPlanarPullback
  rw [Sym2.map_mk]
  have he : s(torusReduceSite L ![a, b], torusReduceSite L ![a + 1, b]) =
      (torusHorizontalEdge L (a : ZMod L) (b : ZMod L) :
        Sym2 (ZMod L × ZMod L)) := by
    simp [torusReduceSite, torusHorizontalEdge_val]
  rw [he, torusAmbientConfigExtend, dif_pos (torusHorizontalEdge L _ _).2]

theorem torusPlanarPullback_vertical (L : ℕ) [Fact (2 < L)]
    (omega : TorusAmbientConfig L) (a b : ℤ) :
    torusPlanarPullback L omega s(![a, b], ![a, b + 1]) =
      omega (torusVerticalEdge L (a : ZMod L) (b : ZMod L)) := by
  unfold torusPlanarPullback
  rw [Sym2.map_mk]
  have he : s(torusReduceSite L ![a, b], torusReduceSite L ![a, b + 1]) =
      (torusVerticalEdge L (a : ZMod L) (b : ZMod L) :
        Sym2 (ZMod L × ZMod L)) := by
    simp [torusReduceSite, torusVerticalEdge_val]
  rw [he, torusAmbientConfigExtend, dif_pos (torusVerticalEdge L _ _).2]

theorem torusAmbientSwapEdgeEquiv_symm_horizontal
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusAmbientSwapEdgeEquiv L).symm (torusHorizontalEdge L x y) =
      torusVerticalEdge L y x := by
  apply Subtype.ext
  simp [torusAmbientSwapEdgeEquiv, torusHorizontalEdge_val,
    torusVerticalEdge_val, torusCoordSwap]

theorem torusAmbientSwapEdgeEquiv_symm_vertical
    (L : ℕ) [Fact (2 < L)] (x y : ZMod L) :
    (torusAmbientSwapEdgeEquiv L).symm (torusVerticalEdge L x y) =
      torusHorizontalEdge L y x := by
  apply Subtype.ext
  simp [torusAmbientSwapEdgeEquiv, torusHorizontalEdge_val,
    torusVerticalEdge_val, torusCoordSwap]

@[simp] theorem torusAmbientSwapCellDual_horizontal
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) (x y : ZMod L) :
    torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)
        (torusHorizontalEdge L x y) =
      !(omega (torusHorizontalEdge L y (x + 1))) := by
  rw [torusAmbientSwapConfig, torusAmbientSwapEdgeEquiv_symm_horizontal,
    torusCellDualAmbientConfig, torusCellCrossing_symm_vertical]

@[simp] theorem torusAmbientSwapCellDual_vertical
    (L : ℕ) [Fact (2 < L)] (omega : TorusAmbientConfig L) (x y : ZMod L) :
    torusAmbientSwapConfig L (torusCellDualAmbientConfig L omega)
        (torusVerticalEdge L x y) =
      !(omega (torusVerticalEdge L (y + 1) x)) := by
  rw [torusAmbientSwapConfig, torusAmbientSwapEdgeEquiv_symm_vertical,
    torusCellDualAmbientConfig, torusCellCrossing_symm_horizontal]


end StatMech.BeffaraDC
