/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition.Part2
open Finset


namespace StatMech.FrontierD

theorem block_boundary_left_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (0, j) = ξ.1 j := by
  have h := congrArg (fun η => η.left j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

theorem block_boundary_right_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (Fin.last N, j) = ξ.1 j := by
  have h := congrArg (fun η => η.right j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

theorem block_boundary_bottom_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, 0) = ξ.2 i := by
  have h := congrArg (fun η => η.bottom i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h

theorem block_boundary_top_value {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, Fin.last M) = ξ.2 i := by
  have h := congrArg (fun η => η.top i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using h


theorem sixVertexRectangleTileBlocks_boundary
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (ω : SixVertexRectangleBlockCopies ξ a b) :
    sixVertexRectangleBoundary (sixVertexRectangleTileBlocks ω) =
      sixVertexToroidalRectangleBoundary
        (sixVertexRepeatToroidalBoundary ξ) := by
  apply SixVertexRectangleBoundary.ext
  · funext gj
    obtain ⟨⟨y, j⟩, rfl⟩ :=
      (finProdFinEquiv (m := b + 1) (n := M + 1)).surjective gj
    have hzero : (0 : Fin ((a + 1) * (N + 1) + 1)) =
        (finProdFinEquiv
          ((0 : Fin (a + 1)), (0 : Fin (N + 1)))).castSucc := by
      ext
      simp [finProdFinEquiv]
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    rw [hzero, sixVertexRectangleTileBlocks_horizontal_castSucc]
    simpa [sixVertexRepeatToroidalBoundary] using
      block_boundary_left_value ω 0 y j
  · funext gj
    obtain ⟨⟨y, j⟩, rfl⟩ :=
      (finProdFinEquiv (m := b + 1) (n := M + 1)).surjective gj
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    simpa [sixVertexRectangleTileBlocks, sixVertexRepeatToroidalBoundary] using
      block_boundary_right_value ω (Fin.last a) y j
  · funext gi
    obtain ⟨⟨x, i⟩, rfl⟩ :=
      (finProdFinEquiv (m := a + 1) (n := N + 1)).surjective gi
    have hzero : (0 : Fin ((b + 1) * (M + 1) + 1)) =
        (finProdFinEquiv
          ((0 : Fin (b + 1)), (0 : Fin (M + 1)))).castSucc := by
      ext
      simp [finProdFinEquiv]
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    rw [hzero, sixVertexRectangleTileBlocks_vertical_castSucc]
    simpa [sixVertexRepeatToroidalBoundary] using
      block_boundary_bottom_value ω x 0 i
  · funext gi
    obtain ⟨⟨x, i⟩, rfl⟩ :=
      (finProdFinEquiv (m := a + 1) (n := N + 1)).surjective gi
    simp only [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary]
    simpa [sixVertexRectangleTileBlocks, sixVertexRepeatToroidalBoundary] using
      block_boundary_top_value ω x (Fin.last b) i


theorem sixVertexRepeatToroidalBoundary_balanced
    {N M a b : ℕ} (hN : Even N)
    (ξ : SixVertexToroidalBoundary N M) (hξ : ξ.Balanced) :
    (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ).Balanced := by
  unfold SixVertexToroidalBoundary.Balanced at hξ ⊢
  rw [Finset.card_filter]
  calc
    (∑ i : Fin ((a + 1) * N),
        if (sixVertexRepeatToroidalBoundary (a := a) (b := b) ξ).2 i = true
        then 1 else 0) =
        ∑ xi : Fin (a + 1) × Fin N,
          if ξ.2 xi.2 = true then 1 else 0 := by
      apply Fintype.sum_equiv
        (finProdFinEquiv (m := a + 1) (n := N)).symm
      intro i
      simp [sixVertexRepeatToroidalBoundary]
    _ = (a + 1) * #{i | ξ.2 i} := by
      rw [Fintype.sum_prod_type, Finset.card_filter]
      simp
    _ = ((a + 1) * N) / 2 := by
      rw [hξ]
      rcases hN with ⟨k, rfl⟩
      have hhalf : (k + k) / 2 = k := by omega
      rw [hhalf]
      have hmul : (a + 1) * (k + k) =
          (a + 1) * k + (a + 1) * k := by ring
      rw [hmul]
      omega


theorem sixVertexRectangleTileBlocks_injective
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)} :
    Function.Injective
      (sixVertexRectangleTileBlocks (ξ := ξ) :
        SixVertexRectangleBlockCopies ξ a b →
          SixVertexRectangleArrows ((a + 1) * (N + 1))
            ((b + 1) * (M + 1))) := by
  intro ω η htile
  funext xy
  apply Subtype.ext
  apply SixVertexRectangleArrows.ext
  · funext kj
    rcases kj with ⟨k, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) k
    · exact (block_boundary_right_value ω xy.1 xy.2 j).trans
        (block_boundary_right_value η xy.1 xy.2 j).symm
    · have h := congrArg (fun ρ => ρ.horizontal
          ((finProdFinEquiv (xy.1, i)).castSucc,
            finProdFinEquiv (xy.2, j))) htile
      simpa using h
  · funext ik
    rcases ik with ⟨i, k⟩
    refine Fin.lastCases ?_ (fun j => ?_) k
    · exact (block_boundary_top_value ω xy.1 xy.2 i).trans
        (block_boundary_top_value η xy.1 xy.2 i).symm
    · have h := congrArg (fun ρ => ρ.vertical
          (finProdFinEquiv (xy.1, i),
            (finProdFinEquiv (xy.2, j)).castSucc)) htile
      simpa using h


end StatMech.FrontierD
