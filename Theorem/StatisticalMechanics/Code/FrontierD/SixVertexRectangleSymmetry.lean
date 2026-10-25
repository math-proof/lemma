/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry
open Finset


namespace StatMech.FrontierD

@[simp] theorem sixVertexRectangleReflectHorizontal_involutive {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleReflectHorizontal (sixVertexRectangleReflectHorizontal ω) = ω := by
  apply SixVertexRectangleArrows.ext <;> funext v <;>
    simp [sixVertexRectangleReflectHorizontal]

@[simp] theorem sixVertexRectangleReflectVertical_involutive {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleReflectVertical (sixVertexRectangleReflectVertical ω) = ω := by
  apply SixVertexRectangleArrows.ext <;> funext v <;>
    simp [sixVertexRectangleReflectVertical]


end StatMech.FrontierD
