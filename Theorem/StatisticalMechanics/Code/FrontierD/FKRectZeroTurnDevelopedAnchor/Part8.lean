/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnDevelopedAnchor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBoundaryToggleWinding.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedOpenBoundaryDependence
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part7
open Equiv Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRawPrimalCrossingTopVertex_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    fkRectRawPrimalCrossingTopVertex R omega X ∈
        fkRectRawPrimalCrossingTorusVertices R omega X ∧
      fkRectRawPrimalCrossingDevelopedHeight R omega X
          (fkRectRawPrimalCrossingTopVertex R omega X) =
        fkRectRawPrimalCrossingMaxDevelopedHeight R omega X := by
  exact (fkRectRawPrimalCrossingTopVertexWithSpec R omega X).2


theorem fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    {x y : R.Vertex}
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (p : (fkRectOpenGraph R omega).Walk x y) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X y -
        fkRectRawPrimalCrossingDevelopedHeight R omega X x =
      (y.2.val : Int) - x.2.val + (R.height : Int) *
        (fkRectWalkWinding R p).2 := by
  unfold fkRectRawPrimalCrossingDevelopedHeight
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hx p
  calc
    (y.2.val : Int) + (R.height : Int) *
          fkRectRawPrimalCrossingVerticalPotential R omega X y -
        ((x.2.val : Int) + (R.height : Int) *
          fkRectRawPrimalCrossingVerticalPotential R omega X x) =
      (y.2.val : Int) - x.2.val + (R.height : Int) *
        (fkRectRawPrimalCrossingVerticalPotential R omega X y -
          fkRectRawPrimalCrossingVerticalPotential R omega X x) := by ring
    _ = _ := by rw [hpot]


theorem fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (x : R.Vertex)
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (hpred : (fkRectOpenGraph R omega).Adj x
      (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X
        (x.1, SixVertexArrows.cyclicPred R.height_pos x.2) =
      fkRectRawPrimalCrossingDevelopedHeight R omega X x - 1 := by
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  let p : (fkRectOpenGraph R omega).Walk x y := .cons hpred .nil
  have h := fkRectRawPrimalCrossingDevelopedHeight_sub_eq_walk
    R omega C X hx p
  have hwind : (fkRectWalkWinding R p).2 =
      fkRectVerticalSeamIncrement R x y := by
    simp [p, y, fkRectWalkWinding]
  rw [hwind] at h
  have hinc := fkRectVerticalSeamIncrement_pred R x.1 x.1 x.2
  change fkRectVerticalSeamIncrement R x y =
      (if x.2.val = 0 then -1 else 0) at hinc
  rw [hinc] at h
  have hpredVal := fkRectCyclicPred_val R.height_pos x.2
  change y.2.val =
      (if x.2.val = 0 then R.height - 1 else x.2.val - 1) at hpredVal
  rw [hpredVal] at h
  dsimp only [y] at h ⊢
  split at h <;> omega


theorem fkRectRawPrimalCrossingBottomEdge_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    omega (true, fkRectRawPrimalCrossingBottomVertex R omega X) = false := by
  let x := fkRectRawPrimalCrossingBottomVertex R omega X
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  let e : R.EdgeIndex := (true, x)
  by_contra hopen
  have hopen' : omega e = true := Bool.eq_true_of_not_eq_false hopen
  have hxy : (fkRectOpenGraph R omega).Adj x y := by
    refine ⟨e, hopen', ?_⟩
    simp [e, x, y, fkRectTorusIndexedEdge]
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound hxy.symm.reachable
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmin : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ≤
      fkRectRawPrimalCrossingDevelopedHeight R omega X y :=
    Finset.min'_le _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingBottomVertex_spec R omega X).2
  have hpred := fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    R omega C X x hxreach hxy
  dsimp only [x, y] at hmin hpred
  rw [← hxheight] at hmin
  omega


theorem fkRectRawPrimalCrossingDevelopedHeight_verticalSucc
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (x : R.Vertex)
    (hx : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x)
    (hsucc : (fkRectOpenGraph R omega).Adj x
      (x.1, finitePeriodicSucc R.height_pos x.2)) :
    fkRectRawPrimalCrossingDevelopedHeight R omega X
        (x.1, finitePeriodicSucc R.height_pos x.2) =
      fkRectRawPrimalCrossingDevelopedHeight R omega X x + 1 := by
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  have hy : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) y :=
    hx.trans hsucc.reachable
  have hpred : (fkRectOpenGraph R omega).Adj y
      (y.1, SixVertexArrows.cyclicPred R.height_pos y.2) := by
    simpa [y, svCyclicPred_finitePeriodicSucc] using hsucc.symm
  have h := fkRectRawPrimalCrossingDevelopedHeight_verticalPred
    R omega C X y hy hpred
  simp only [y, svCyclicPred_finitePeriodicSucc] at h
  calc
    fkRectRawPrimalCrossingDevelopedHeight R omega X
          (x.1, finitePeriodicSucc R.height_pos x.2) =
        (fkRectRawPrimalCrossingDevelopedHeight R omega X
          (x.1, finitePeriodicSucc R.height_pos x.2) - 1) + 1 := by ring
    _ = fkRectRawPrimalCrossingDevelopedHeight R omega X x + 1 := by
      rw [← h]

theorem fkRectVerticalSeamIncrement_succ_back
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVerticalSeamIncrement R
        ((x.1, finitePeriodicSucc R.height_pos x.2)) x =
      if x.2.val + 1 = R.height then -1 else 0 := by
  unfold fkRectVerticalSeamIncrement
  rw [finitePeriodicSucc_val]
  have hgt := R.height_gt_two
  have hlt := x.2.isLt
  by_cases hwrap : x.2.val + 1 = R.height
  · simp [hwrap]
    omega
  · simp [hwrap]
    omega

theorem fkRectVerticalSeamIncrement_pred_forward
    (R : FKRectTorus) (x : R.Vertex) :
    fkRectVerticalSeamIncrement R
        ((x.1, SixVertexArrows.cyclicPred R.height_pos x.2)) x =
      if x.2.val = 0 then 1 else 0 := by
  unfold fkRectVerticalSeamIncrement
  rw [fkRectCyclicPred_val]
  have hgt := R.height_gt_two
  have hlt := x.2.isLt
  by_cases hzero : x.2.val = 0
  · simp [hzero]
    omega
  · simp [hzero]
    omega


theorem fkRectRawPrimalCrossingTopClosing_verticalWinding_neg
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingTopVertex R omega X)
      ((fkRectRawPrimalCrossingTopVertex R omega X).1,
        finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2)) :
    (fkRectWalkWinding R p).2 +
        fkRectVerticalSeamIncrement R
          ((fkRectRawPrimalCrossingTopVertex R omega X).1,
            finitePeriodicSucc R.height_pos
              (fkRectRawPrimalCrossingTopVertex R omega X).2)
          (fkRectRawPrimalCrossingTopVertex R omega X) < 0 := by
  let x := fkRectRawPrimalCrossingTopVertex R omega X
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingTopVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound ⟨p.reverse⟩
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmax : fkRectRawPrimalCrossingDevelopedHeight R omega X y ≤
      fkRectRawPrimalCrossingMaxDevelopedHeight R omega X :=
    Finset.le_max' _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingTopVertex_spec R omega X).2
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hxreach p
  dsimp only [x, y] at hmax hpot ⊢
  rw [← hxheight] at hmax
  unfold fkRectRawPrimalCrossingDevelopedHeight at hmax
  have hpot' :
      fkRectRawPrimalCrossingVerticalPotential R omega X
          ((fkRectRawPrimalCrossingTopVertex R omega X).1,
            finitePeriodicSucc R.height_pos
              (fkRectRawPrimalCrossingTopVertex R omega X).2) =
        (fkRectWalkWinding R p).2 +
          fkRectRawPrimalCrossingVerticalPotential R omega X
            (fkRectRawPrimalCrossingTopVertex R omega X) := by
    linarith
  rw [hpot'] at hmax
  have hheight : (0 : Int) < R.height := by exact_mod_cast R.height_pos
  by_cases hwrap :
    (fkRectRawPrimalCrossingTopVertex R omega X).2.val + 1 = R.height
  · have hinc := fkRectVerticalSeamIncrement_succ_back R
      (fkRectRawPrimalCrossingTopVertex R omega X)
    rw [if_pos hwrap] at hinc
    simp [finitePeriodicSucc_val, hwrap] at hmax
    rw [hinc]
    ring_nf at hmax
    nlinarith
  · have hinc := fkRectVerticalSeamIncrement_succ_back R
      (fkRectRawPrimalCrossingTopVertex R omega X)
    rw [if_neg hwrap] at hinc
    simp [finitePeriodicSucc_val, hwrap] at hmax
    rw [hinc]
    ring_nf at hmax
    nlinarith


theorem fkRectRawPrimalCrossingBottomClosing_verticalWinding_pos
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega)
    (p : (fkRectOpenGraph R omega).Walk
      (fkRectRawPrimalCrossingBottomVertex R omega X)
      ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
        SixVertexArrows.cyclicPred R.height_pos
          (fkRectRawPrimalCrossingBottomVertex R omega X).2)) :
    0 < (fkRectWalkWinding R p).2 +
        fkRectVerticalSeamIncrement R
          ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
            SixVertexArrows.cyclicPred R.height_pos
              (fkRectRawPrimalCrossingBottomVertex R omega X).2)
          (fkRectRawPrimalCrossingBottomVertex R omega X) := by
  let x := fkRectRawPrimalCrossingBottomVertex R omega X
  let y : R.Vertex :=
    (x.1, SixVertexArrows.cyclicPred R.height_pos x.2)
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingBottomVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound ⟨p.reverse⟩
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmin : fkRectRawPrimalCrossingMinDevelopedHeight R omega X ≤
      fkRectRawPrimalCrossingDevelopedHeight R omega X y :=
    Finset.min'_le _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingBottomVertex_spec R omega X).2
  have hpot := fkRectRawPrimalCrossingVerticalPotential_sub_eq_walk
    R omega C X hxreach p
  dsimp only [x, y] at hmin hpot ⊢
  rw [← hxheight] at hmin
  unfold fkRectRawPrimalCrossingDevelopedHeight at hmin
  have hpot' :
      fkRectRawPrimalCrossingVerticalPotential R omega X
          ((fkRectRawPrimalCrossingBottomVertex R omega X).1,
            SixVertexArrows.cyclicPred R.height_pos
              (fkRectRawPrimalCrossingBottomVertex R omega X).2) =
        (fkRectWalkWinding R p).2 +
          fkRectRawPrimalCrossingVerticalPotential R omega X
            (fkRectRawPrimalCrossingBottomVertex R omega X) := by
    linarith
  rw [hpot'] at hmin
  have hheight : (0 : Int) < R.height := by exact_mod_cast R.height_pos
  by_cases hzero :
    (fkRectRawPrimalCrossingBottomVertex R omega X).2.val = 0
  · have hinc := fkRectVerticalSeamIncrement_pred_forward R
      (fkRectRawPrimalCrossingBottomVertex R omega X)
    rw [if_pos hzero] at hinc
    simp [fkRectCyclicPred_val, hzero] at hmin
    rw [Nat.cast_sub (by omega : 1 ≤ R.height)] at hmin
    norm_num at hmin
    rw [hinc]
    ring_nf at hmin
    nlinarith
  · have hinc := fkRectVerticalSeamIncrement_pred_forward R
      (fkRectRawPrimalCrossingBottomVertex R omega X)
    rw [if_neg hzero] at hinc
    simp [fkRectCyclicPred_val, hzero] at hmin
    have hpos : 1 ≤
        (fkRectRawPrimalCrossingBottomVertex R omega X).2.val := by omega
    rw [Nat.cast_sub hpos] at hmin
    norm_num at hmin
    rw [hinc]
    ring_nf at hmin
    nlinarith


theorem fkRectRawPrimalCrossingTopEdge_closed
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega)
    (X : FKRectRawPrimalHorizontalCrossingComponent R omega) :
    omega (true,
      ((fkRectRawPrimalCrossingTopVertex R omega X).1,
        finitePeriodicSucc R.height_pos
          (fkRectRawPrimalCrossingTopVertex R omega X).2)) = false := by
  let x := fkRectRawPrimalCrossingTopVertex R omega X
  let y : R.Vertex := (x.1, finitePeriodicSucc R.height_pos x.2)
  let e : R.EdgeIndex := (true, y)
  by_contra hopen
  have hopen' : omega e = true := Bool.eq_true_of_not_eq_false hopen
  have hxy : (fkRectOpenGraph R omega).Adj x y := by
    refine ⟨e, hopen', ?_⟩
    simp [e, x, y, fkRectTorusIndexedEdge,
      svCyclicPred_finitePeriodicSucc]
  have hxmem : x ∈ fkRectRawPrimalCrossingTorusVertices R omega X :=
    (fkRectRawPrimalCrossingTopVertex_spec R omega X).1
  have hxreach : (fkRectOpenGraph R omega).Reachable
      (fkRectRawPrimalCrossingBase R omega X) x :=
    fkRectRawPrimalCrossingBase_reachable_of_mem_torusVertices
      R omega X hxmem
  have hymem : y ∈ fkRectRawPrimalCrossingTorusVertices R omega X := by
    rw [mem_fkRectRawPrimalCrossingTorusVertices]
    calc
      (fkRectOpenGraph R omega).connectedComponentMk y =
          (fkRectOpenGraph R omega).connectedComponentMk x :=
        SimpleGraph.ConnectedComponent.sound hxy.symm.reachable
      _ = fkRectRawPrimalCrossingTorusComponent R omega X :=
        (mem_fkRectRawPrimalCrossingTorusVertices R omega X x).1 hxmem
  have hyHeightMem : fkRectRawPrimalCrossingDevelopedHeight R omega X y ∈
      fkRectRawPrimalCrossingDevelopedHeights R omega X :=
    Finset.mem_image.mpr ⟨y, hymem, rfl⟩
  have hmax : fkRectRawPrimalCrossingDevelopedHeight R omega X y ≤
      fkRectRawPrimalCrossingMaxDevelopedHeight R omega X :=
    Finset.le_max' _ _ hyHeightMem
  have hxheight := (fkRectRawPrimalCrossingTopVertex_spec R omega X).2
  have hsucc := fkRectRawPrimalCrossingDevelopedHeight_verticalSucc
    R omega C X x hxreach hxy
  dsimp only [x, y] at hmax hsucc
  rw [← hxheight] at hmax
  omega


end
end StatMech.FrontierD
