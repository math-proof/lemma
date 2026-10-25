/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing.Part2
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangle_reflectedQuadrantsCompatible {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M)
    (ω₀ ω₁ ω₂ ω₃ : SixVertexRectangleArrows N M)
    (h₀ : sixVertexRectangleBoundary ω₀ = ξ)
    (h₁ : sixVertexRectangleBoundary ω₁ = ξ)
    (h₂ : sixVertexRectangleBoundary ω₂ = ξ)
    (h₃ : sixVertexRectangleBoundary ω₃ = ξ) :
    SixVertexRectangleQuadrantsCompatible
      ω₀
      (sixVertexRectangleReflectHorizontal ω₁)
      (sixVertexRectangleReflectVertical ω₂)
      (sixVertexRectangleReflectHorizontal
        (sixVertexRectangleReflectVertical ω₃)) := by
  rw [SixVertexRectangleQuadrantsCompatible,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    sixVertexRectangleReflectHorizontal_boundary,
    sixVertexRectangleReflectVertical_boundary,
    h₀, h₁, h₂, h₃]
  simp [sixVertexBoundaryReflectHorizontal, sixVertexBoundaryReflectVertical]


end StatMech.FrontierD
