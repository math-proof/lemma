/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part4
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleReflectedGlue_compatible {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    SixVertexRectangleQuadrantsCompatible omega.1.1
      (sixVertexRectangleReflectHorizontal omega.2.1.1)
      (sixVertexRectangleReflectVertical omega.2.2.1.1)
      (sixVertexRectangleReflectHorizontal
        (sixVertexRectangleReflectVertical omega.2.2.2.1)) := by
  exact sixVertexRectangle_reflectedQuadrantsCompatible ξ
    omega.1.1 omega.2.1.1 omega.2.2.1.1 omega.2.2.2.1
    omega.1.2 omega.2.1.2 omega.2.2.1.2 omega.2.2.2.2


theorem sixVertexRectangleReflectedGlue_boundary {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    {ξ : SixVertexToroidalBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies
      (sixVertexToroidalRectangleBoundary ξ)) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectedGlue omega) =
      sixVertexToroidalRectangleBoundary
        (sixVertexDoubledToroidalBoundary ξ) := by
  rw [sixVertexRectangleReflectedGlue,
    sixVertexRectangleGlueQuadrants_boundary hN hM,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    omega.1.2, omega.2.1.2, omega.2.2.1.2, omega.2.2.2.2]
  exact sixVertexRectangle_reflectedGlueBoundary_eq_toroidal ξ


theorem sixVertexRectangleReflectedGlue_weight {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M) (c : ℝ)
    {ξ : SixVertexRectangleBoundary N M}
    (omega : SixVertexRectangleFourBoundaryCopies ξ) :
    (sixVertexRectangleReflectedGlue omega).weight c =
      omega.1.1.weight c * omega.2.1.1.weight c *
        omega.2.2.1.1.weight c * omega.2.2.2.1.weight c := by
  rw [sixVertexRectangleReflectedGlue,
    sixVertexRectangleGlueQuadrants_weight hN hM c _ _ _ _
      (sixVertexRectangleReflectedGlue_compatible omega),
    sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectVertical_weight,
    sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectVertical_weight]


theorem sixVertexRectangleReflectedGlue_injective {N M : ℕ}
    {ξ : SixVertexRectangleBoundary N M} :
    Function.Injective
      (sixVertexRectangleReflectedGlue :
        SixVertexRectangleFourBoundaryCopies ξ →
          SixVertexRectangleArrows (N + N) (M + M)) := by
  intro omega eta hglue
  have h₀ : omega.1.1 = eta.1.1 :=
    sixVertexRectangleGlueQuadrants_lowerLeft_injective hglue
      (omega.1.2.trans eta.1.2.symm)
  have hb₁ :
      sixVertexRectangleBoundary
          (sixVertexRectangleReflectHorizontal omega.2.1.1) =
        sixVertexRectangleBoundary
          (sixVertexRectangleReflectHorizontal eta.2.1.1) := by
    calc
      _ = sixVertexBoundaryReflectHorizontal
          (sixVertexRectangleBoundary omega.2.1.1) :=
        sixVertexRectangleReflectHorizontal_boundary _
      _ = sixVertexBoundaryReflectHorizontal ξ := by rw [omega.2.1.2]
      _ = sixVertexBoundaryReflectHorizontal
          (sixVertexRectangleBoundary eta.2.1.1) := by rw [eta.2.1.2]
      _ = _ := (sixVertexRectangleReflectHorizontal_boundary _).symm
  have href₁ :
      sixVertexRectangleReflectHorizontal omega.2.1.1 =
        sixVertexRectangleReflectHorizontal eta.2.1.1 :=
    sixVertexRectangleGlueQuadrants_lowerRight_injective hglue hb₁
  have h₁ : omega.2.1.1 = eta.2.1.1 := by
    simpa using congrArg sixVertexRectangleReflectHorizontal href₁
  have hb₂ :
      sixVertexRectangleBoundary
          (sixVertexRectangleReflectVertical omega.2.2.1.1) =
        sixVertexRectangleBoundary
          (sixVertexRectangleReflectVertical eta.2.2.1.1) := by
    calc
      _ = sixVertexBoundaryReflectVertical
          (sixVertexRectangleBoundary omega.2.2.1.1) :=
        sixVertexRectangleReflectVertical_boundary _
      _ = sixVertexBoundaryReflectVertical ξ := by rw [omega.2.2.1.2]
      _ = sixVertexBoundaryReflectVertical
          (sixVertexRectangleBoundary eta.2.2.1.1) := by rw [eta.2.2.1.2]
      _ = _ := (sixVertexRectangleReflectVertical_boundary _).symm
  have href₂ :
      sixVertexRectangleReflectVertical omega.2.2.1.1 =
        sixVertexRectangleReflectVertical eta.2.2.1.1 :=
    sixVertexRectangleGlueQuadrants_upperLeft_injective hglue hb₂
  have h₂ : omega.2.2.1.1 = eta.2.2.1.1 := by
    simpa using congrArg sixVertexRectangleReflectVertical href₂
  have href₃ :
      sixVertexRectangleReflectHorizontal
          (sixVertexRectangleReflectVertical omega.2.2.2.1) =
        sixVertexRectangleReflectHorizontal
          (sixVertexRectangleReflectVertical eta.2.2.2.1) :=
    sixVertexRectangleGlueQuadrants_upperRight_injective hglue
  have h₃ : omega.2.2.2.1 = eta.2.2.2.1 := by
    have h := congrArg
      (fun rho => sixVertexRectangleReflectVertical
        (sixVertexRectangleReflectHorizontal rho)) href₃
    simpa using h
  apply Prod.ext
  · exact Subtype.ext h₀
  · apply Prod.ext
    · exact Subtype.ext h₁
    · apply Prod.ext
      · exact Subtype.ext h₂
      · exact Subtype.ext h₃


end StatMech.FrontierD
