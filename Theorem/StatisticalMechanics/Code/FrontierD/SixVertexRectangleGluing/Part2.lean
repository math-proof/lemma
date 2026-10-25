/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleGluing
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleGlueQuadrants_boundary {N M : ℕ}
    (hN : 0 < N) (hM : 0 < M)
    (lowerLeft lowerRight upperLeft upperRight : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary
        (sixVertexRectangleGlueQuadrants lowerLeft lowerRight upperLeft upperRight) =
      sixVertexRectangleGlueBoundary
        (sixVertexRectangleBoundary lowerLeft)
        (sixVertexRectangleBoundary lowerRight)
        (sixVertexRectangleBoundary upperLeft)
        (sixVertexRectangleBoundary upperRight) := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  apply SixVertexRectangleBoundary.ext
  · funext y
    refine Fin.addCases ?_ ?_ y <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext y
    refine Fin.addCases ?_ ?_ y <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext x
    refine Fin.addCases ?_ ?_ x <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]
  · funext x
    refine Fin.addCases ?_ ?_ x <;> intro i <;>
      simp [sixVertexRectangleBoundary, sixVertexRectangleGlueQuadrants,
        sixVertexRectangleGlueBoundary]


end StatMech.FrontierD
