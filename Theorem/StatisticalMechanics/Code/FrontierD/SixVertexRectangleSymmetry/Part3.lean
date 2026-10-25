/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part3
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleReflectHorizontal_weight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) :
    (sixVertexRectangleReflectHorizontal ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin N × Fin M, (sixVertexRectangleReflectHorizontal ω).localWeight c v =
        ∏ v : Fin N × Fin M, ω.localWeight c (v.1.rev, v.2) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact sixVertexRectangleReflectHorizontal_localWeight c ω v
    _ = ∏ v : Fin N × Fin M, ω.localWeight c v :=
      ((Fin.revPerm.prodCongr (Equiv.refl (Fin M))).prod_comp
        fun v => ω.localWeight c v)

theorem sixVertexRectangleReflectVertical_weight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) :
    (sixVertexRectangleReflectVertical ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexRectangleArrows.weight]
  calc
    ∏ v : Fin N × Fin M, (sixVertexRectangleReflectVertical ω).localWeight c v =
        ∏ v : Fin N × Fin M, ω.localWeight c (v.1, v.2.rev) := by
          apply Finset.prod_congr rfl
          intro v hv
          exact sixVertexRectangleReflectVertical_localWeight c ω v
    _ = ∏ v : Fin N × Fin M, ω.localWeight c v :=
      (((Equiv.refl (Fin N)).prodCongr Fin.revPerm).prod_comp
        fun v => ω.localWeight c v)


theorem sixVertexRectangleBoundaryPartitionSum_reflectHorizontal
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexBoundaryReflectHorizontal ξ) =
      sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleBoundaryPartitionSum,
    sixVertexRectangleBoundaryPartitionSum]
  apply Fintype.sum_equiv (sixVertexRectangleReflectHorizontalEquiv N M)
  intro ω
  change (if sixVertexRectangleBoundary ω = sixVertexBoundaryReflectHorizontal ξ
      then ω.weight c else 0) =
    if sixVertexRectangleBoundary (sixVertexRectangleReflectHorizontal ω) = ξ
      then (sixVertexRectangleReflectHorizontal ω).weight c else 0
  rw [sixVertexRectangleReflectHorizontal_weight,
    sixVertexRectangleReflectHorizontal_boundary]
  have hiff :
      sixVertexBoundaryReflectHorizontal (sixVertexRectangleBoundary ω) = ξ ↔
        sixVertexRectangleBoundary ω = sixVertexBoundaryReflectHorizontal ξ := by
    constructor
    · intro h
      simpa using congrArg sixVertexBoundaryReflectHorizontal h
    · intro h
      simp [h]
  rw [if_congr hiff rfl rfl]


theorem sixVertexRectangleBoundaryPartitionSum_reflectVertical
    (N M : ℕ) (c : ℝ) (ξ : SixVertexRectangleBoundary N M) :
    sixVertexRectangleBoundaryPartitionSum N M c
        (sixVertexBoundaryReflectVertical ξ) =
      sixVertexRectangleBoundaryPartitionSum N M c ξ := by
  classical
  rw [sixVertexRectangleBoundaryPartitionSum,
    sixVertexRectangleBoundaryPartitionSum]
  apply Fintype.sum_equiv (sixVertexRectangleReflectVerticalEquiv N M)
  intro ω
  change (if sixVertexRectangleBoundary ω = sixVertexBoundaryReflectVertical ξ
      then ω.weight c else 0) =
    if sixVertexRectangleBoundary (sixVertexRectangleReflectVertical ω) = ξ
      then (sixVertexRectangleReflectVertical ω).weight c else 0
  rw [sixVertexRectangleReflectVertical_weight,
    sixVertexRectangleReflectVertical_boundary]
  have hiff :
      sixVertexBoundaryReflectVertical (sixVertexRectangleBoundary ω) = ξ ↔
        sixVertexRectangleBoundary ω = sixVertexBoundaryReflectVertical ξ := by
    constructor
    · intro h
      simpa using congrArg sixVertexBoundaryReflectVertical h
    · intro h
      simp [h]
  rw [if_congr hiff rfl rfl]

end StatMech.FrontierD
