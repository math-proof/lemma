/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part3
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangle_reflectedGlueBoundary_eq_toroidal {N M : ℕ}
    (ξ : SixVertexToroidalBoundary N M) :
    sixVertexRectangleGlueBoundary
        (sixVertexToroidalRectangleBoundary ξ)
        (sixVertexBoundaryReflectHorizontal
          (sixVertexToroidalRectangleBoundary ξ))
        (sixVertexBoundaryReflectVertical
          (sixVertexToroidalRectangleBoundary ξ))
        (sixVertexBoundaryReflectHorizontal
          (sixVertexBoundaryReflectVertical
            (sixVertexToroidalRectangleBoundary ξ))) =
      sixVertexToroidalRectangleBoundary
        (sixVertexDoubledToroidalBoundary ξ) := by
  apply SixVertexRectangleBoundary.ext <;> funext k
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]
  · refine Fin.addCases ?_ ?_ k <;> intro i <;>
      simp [sixVertexRectangleGlueBoundary, sixVertexToroidalRectangleBoundary,
        sixVertexDoubledToroidalBoundary, sixVertexBoundaryReflectHorizontal,
        sixVertexBoundaryReflectVertical]


theorem sixVertexRectangleGlueQuadrants_localWeight_lowerLeft {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.castAdd N i, Fin.castAdd M j) =
      lowerLeft.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hright (j : Fin (M + 1)) :
      lowerLeft.horizontal (Fin.last (N + 1), j) =
        lowerRight.horizontal (0, j) := by
    have h := congrFun hcompat.1 j
    simpa [sixVertexRectangleBoundary] using h
  have htop (i : Fin (N + 1)) :
      lowerLeft.vertical (i, Fin.last (M + 1)) =
        upperLeft.vertical (i, 0) := by
    have h := congrFun hcompat.2.2.1 i
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, hright, htop]
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, hright]
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants, htop]
    · simp [SixVertexRectangleArrows.localWeight,
        SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
        sixVertexRectangleGlueQuadrants]


theorem sixVertexRectangleGlueQuadrants_localWeight_lowerRight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.natAdd N i, Fin.castAdd M j) =
      lowerRight.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have htop (i : Fin (N + 1)) :
      lowerRight.vertical (i, Fin.last (M + 1)) =
        upperRight.vertical (i, 0) := by
    have h := congrFun hcompat.2.2.2 i
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants, htop]
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants]


theorem sixVertexRectangleGlueQuadrants_localWeight_upperLeft {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.castAdd N i, Fin.natAdd M j) =
      upperLeft.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  have hright (j : Fin (M + 1)) :
      upperLeft.horizontal (Fin.last (N + 1), j) =
        upperRight.horizontal (0, j) := by
    have h := congrFun hcompat.2.1 j
    simpa [sixVertexRectangleBoundary] using h
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants, hright]
  · simp [SixVertexRectangleArrows.localWeight,
      SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
      sixVertexRectangleGlueQuadrants]


theorem sixVertexRectangleGlueQuadrants_localWeight_upperRight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (i : Fin N) (j : Fin M) :
    (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight).localWeight c
        (Fin.natAdd N i, Fin.natAdd M j) =
      upperRight.localWeight c (i, j) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  simp [SixVertexRectangleArrows.localWeight,
    SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleGlueQuadrants]


theorem sixVertexRectangleGlueQuadrants_weight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M)
    (hcompat : SixVertexRectangleQuadrantsCompatible
      lowerLeft lowerRight upperLeft upperRight) :
    (sixVertexRectangleGlueQuadrants
        lowerLeft lowerRight upperLeft upperRight).weight c =
      lowerLeft.weight c * lowerRight.weight c *
        upperLeft.weight c * upperRight.weight c := by
  let e : (Fin N ⊕ Fin N) × (Fin M ⊕ Fin M) ≃
      Fin (N + N) × Fin (M + M) :=
    finSumFinEquiv.prodCongr finSumFinEquiv
  rw [SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin (N + N) × Fin (M + M),
        (sixVertexRectangleGlueQuadrants
          lowerLeft lowerRight upperLeft upperRight).localWeight c v =
      ∏ v : (Fin N ⊕ Fin N) × (Fin M ⊕ Fin M),
        (sixVertexRectangleGlueQuadrants
          lowerLeft lowerRight upperLeft upperRight).localWeight c (e v) :=
        (e.prod_comp _).symm
    _ = (∏ i : Fin N, ∏ j : Fin M, lowerLeft.localWeight c (i, j)) *
          (∏ i : Fin N, ∏ j : Fin M, upperLeft.localWeight c (i, j)) *
          ((∏ i : Fin N, ∏ j : Fin M, lowerRight.localWeight c (i, j)) *
          (∏ i : Fin N, ∏ j : Fin M, upperRight.localWeight c (i, j))) := by
      simp only [e, Equiv.prodCongr_apply, Prod.map_apply,
        Fintype.prod_prod_type,
        Fintype.prod_sum_type, finSumFinEquiv_apply_left,
        finSumFinEquiv_apply_right]
      simp only [
        sixVertexRectangleGlueQuadrants_localWeight_lowerLeft
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_lowerRight
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_upperLeft
          hN hM c lowerLeft lowerRight upperLeft upperRight hcompat,
        sixVertexRectangleGlueQuadrants_localWeight_upperRight
          hN hM c lowerLeft lowerRight upperLeft upperRight]
      rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ = lowerLeft.weight c * lowerRight.weight c *
          upperLeft.weight c * upperRight.weight c := by
      simp only [SixVertexRectangleArrows.weight, Fintype.prod_prod_type]
      ring

theorem sixVertexRectangleGlueQuadrants_lowerLeft_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₀ =
      sixVertexRectangleBoundary b₀) :
    a₀ = b₀ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) x
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.right hboundary) y
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.horizontal
          (Fin.castAdd (N + 1) i, Fin.castAdd M y)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun j => ?_) y
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.top hboundary) x
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.vertical
          (Fin.castAdd N x, Fin.castAdd (M + 1) j)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h

theorem sixVertexRectangleGlueQuadrants_lowerRight_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₁ =
      sixVertexRectangleBoundary b₁) :
    a₁ = b₁ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.horizontal
        (Fin.natAdd N x, Fin.castAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun j => ?_) y
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.top hboundary) x
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.vertical
          (Fin.natAdd N x, Fin.castAdd (M + 1) j)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h

theorem sixVertexRectangleGlueQuadrants_upperLeft_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃)
    (hboundary : sixVertexRectangleBoundary a₂ =
      sixVertexRectangleBoundary b₂) :
    a₂ = b₂ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    refine Fin.lastCases ?_ (fun i => ?_) x
    · have h := congrFun
        (congrArg SixVertexRectangleBoundary.right hboundary) y
      simpa [sixVertexRectangleBoundary] using h
    · have h := congrArg (fun omega => omega.horizontal
          (Fin.castAdd (N + 1) i, Fin.natAdd M y)) hglue
      simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.vertical
        (Fin.castAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h

theorem sixVertexRectangleGlueQuadrants_upperRight_injective
    {N M : ℕ}
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : SixVertexRectangleArrows N M}
    (hglue : sixVertexRectangleGlueQuadrants a₀ a₁ a₂ a₃ =
      sixVertexRectangleGlueQuadrants b₀ b₁ b₂ b₃) :
    a₃ = b₃ := by
  apply SixVertexRectangleArrows.ext
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.horizontal
        (Fin.natAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h
  · funext xy
    rcases xy with ⟨x, y⟩
    have h := congrArg (fun omega => omega.vertical
        (Fin.natAdd N x, Fin.natAdd M y)) hglue
    simpa [sixVertexRectangleGlueQuadrants] using h


end StatMech.FrontierD
