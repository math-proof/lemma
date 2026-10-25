/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBlockRepetition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBalancedTransferBridge.Part10
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBlockRepetition
open Finset


namespace StatMech.FrontierD

theorem block_boundary_left_right {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (0, j) =
      (ω (x, y)).1.horizontal (Fin.last N, j) := by
  have hl := congrArg (fun η => η.left j) (ω (x, y)).2
  have hr := congrArg (fun η => η.right j) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hl.trans hr.symm

theorem block_boundary_bottom_top {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, 0) =
      (ω (x, y)).1.vertical (i, Fin.last M) := by
  have hb := congrArg (fun η => η.bottom i) (ω (x, y)).2
  have ht := congrArg (fun η => η.top i) (ω (x, y)).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hb.trans ht.symm

theorem block_boundary_right_left {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x x' : Fin (a + 1)) (y y' : Fin (b + 1)) (j : Fin M) :
    (ω (x, y)).1.horizontal (Fin.last N, j) =
      (ω (x', y')).1.horizontal (0, j) := by
  have hr := congrArg (fun η => η.right j) (ω (x, y)).2
  have hl := congrArg (fun η => η.left j) (ω (x', y')).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    hr.trans hl.symm

theorem block_boundary_top_bottom {N M a b : ℕ}
    {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x x' : Fin (a + 1)) (y y' : Fin (b + 1)) (i : Fin N) :
    (ω (x, y)).1.vertical (i, Fin.last M) =
      (ω (x', y')).1.vertical (i, 0) := by
  have ht := congrArg (fun η => η.top i) (ω (x, y)).2
  have hb := congrArg (fun η => η.bottom i) (ω (x', y')).2
  simpa [sixVertexRectangleBoundary, sixVertexToroidalRectangleBoundary] using
    ht.trans hb.symm

@[simp] theorem sixVertexRectangleTileBlocks_horizontal_castSucc
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).horizontal
        ((finProdFinEquiv (x, i)).castSucc, finProdFinEquiv (y, j)) =
      (ω (x, y)).1.horizontal (i.castSucc, j) := by
  simp [sixVertexRectangleTileBlocks]

@[simp] theorem sixVertexRectangleTileBlocks_vertical_castSucc
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1)) (i : Fin N) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).vertical
        (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).castSucc) =
      (ω (x, y)).1.vertical (i, j.castSucc) := by
  simp [sixVertexRectangleTileBlocks]

@[simp] theorem sixVertexRectangleTileBlocks_horizontal_succ
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) M}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin (N + 1)) (j : Fin M) :
    (sixVertexRectangleTileBlocks ω).horizontal
        ((finProdFinEquiv (x, i)).succ, finProdFinEquiv (y, j)) =
      (ω (x, y)).1.horizontal (i.succ, j) := by
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun x => ?_) x
    · have hlast :
          (finProdFinEquiv (Fin.last a, Fin.last N)).succ =
            Fin.last ((a + 1) * (N + 1)) := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hlast]
      simp [sixVertexRectangleTileBlocks]
    · have hnext :
          (finProdFinEquiv (x.castSucc, Fin.last N)).succ =
            (finProdFinEquiv (x.succ, (0 : Fin (N + 1)))).castSucc := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hnext, sixVertexRectangleTileBlocks_horizontal_castSucc]
      exact (block_boundary_right_left ω x.castSucc x.succ y y j).symm
  · have hnext :
        (finProdFinEquiv (x, i.castSucc)).succ =
          (finProdFinEquiv (x, i.succ)).castSucc := by
      ext
      simp [finProdFinEquiv]
      ring
  
    rw [hnext, sixVertexRectangleTileBlocks_horizontal_castSucc]
    rfl

@[simp] theorem sixVertexRectangleTileBlocks_vertical_succ
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary N (M + 1)}
    (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin N) (j : Fin (M + 1)) :
    (sixVertexRectangleTileBlocks ω).vertical
        (finProdFinEquiv (x, i), (finProdFinEquiv (y, j)).succ) =
      (ω (x, y)).1.vertical (i, j.succ) := by
  refine Fin.lastCases ?_ (fun j => ?_) j
  · refine Fin.lastCases ?_ (fun y => ?_) y
    · have hlast :
          (finProdFinEquiv (Fin.last b, Fin.last M)).succ =
            Fin.last ((b + 1) * (M + 1)) := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hlast]
      simp [sixVertexRectangleTileBlocks]
    · have hnext :
          (finProdFinEquiv (y.castSucc, Fin.last M)).succ =
            (finProdFinEquiv (y.succ, (0 : Fin (M + 1)))).castSucc := by
        ext
        simp [finProdFinEquiv]
        ring
      rw [hnext, sixVertexRectangleTileBlocks_vertical_castSucc]
      exact (block_boundary_top_bottom ω x x y.castSucc y.succ i).symm
  · have hnext :
        (finProdFinEquiv (y, j.castSucc)).succ =
          (finProdFinEquiv (y, j.succ)).castSucc := by
      ext
      simp [finProdFinEquiv]
      ring
    rw [hnext, sixVertexRectangleTileBlocks_vertical_castSucc]
    rfl


theorem sixVertexRectangleTileBlocks_localWeight
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (c : ℝ) (ω : SixVertexRectangleBlockCopies ξ a b)
    (x : Fin (a + 1)) (y : Fin (b + 1))
    (i : Fin (N + 1)) (j : Fin (M + 1)) :
    (sixVertexRectangleTileBlocks ω).localWeight c
        (finProdFinEquiv (x, i), finProdFinEquiv (y, j)) =
      (ω (x, y)).1.localWeight c (i, j) := by
  simp [SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount,
    SixVertexRectangleArrows.IsCType]


theorem sixVertexRectangleTileBlocks_weight
    {N M a b : ℕ} {ξ : SixVertexToroidalBoundary (N + 1) (M + 1)}
    (c : ℝ) (ω : SixVertexRectangleBlockCopies ξ a b) :
    (sixVertexRectangleTileBlocks ω).weight c =
      ∏ xy : Fin (a + 1) × Fin (b + 1), (ω xy).1.weight c := by
  rw [SixVertexRectangleArrows.weight]
  let e := Equiv.prodCongr
    (finProdFinEquiv (m := a + 1) (n := N + 1))
    (finProdFinEquiv (m := b + 1) (n := M + 1))
  calc
    (∏ v, (sixVertexRectangleTileBlocks ω).localWeight c v) =
        ∏ p : (Fin (a + 1) × Fin (N + 1)) ×
            (Fin (b + 1) × Fin (M + 1)),
          (sixVertexRectangleTileBlocks ω).localWeight c (e p) := by
      exact (Fintype.prod_equiv e _ _ fun _ => rfl).symm
    _ = ∏ p : (Fin (a + 1) × Fin (N + 1)) ×
            (Fin (b + 1) × Fin (M + 1)),
          (ω (p.1.1, p.2.1)).1.localWeight c (p.1.2, p.2.2) := by
      apply Fintype.prod_congr
      intro p
      exact sixVertexRectangleTileBlocks_localWeight c ω
        p.1.1 p.2.1 p.1.2 p.2.2
    _ = ∏ xy : Fin (a + 1) × Fin (b + 1), (ω xy).1.weight c := by
      simp only [Fintype.prod_prod_type, SixVertexRectangleArrows.weight]
      apply Finset.prod_congr rfl
      intro x hx
      rw [Finset.prod_comm]


end StatMech.FrontierD
