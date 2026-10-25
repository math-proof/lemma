/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Mathlib.Data.Fin.Rev
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleSymmetry.Part2
open Finset


namespace StatMech.FrontierD

theorem sixVertexRectangleReflectHorizontal_boundary {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectHorizontal ω) =
      sixVertexBoundaryReflectHorizontal (sixVertexRectangleBoundary ω) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexRectangleReflectHorizontal,
      sixVertexBoundaryReflectHorizontal]

theorem sixVertexRectangleReflectVertical_boundary {N M : ℕ}
    (ω : SixVertexRectangleArrows N M) :
    sixVertexRectangleBoundary (sixVertexRectangleReflectVertical ω) =
      sixVertexBoundaryReflectVertical (sixVertexRectangleBoundary ω) := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexRectangleBoundary, sixVertexRectangleReflectVertical,
      sixVertexBoundaryReflectVertical]

@[simp] theorem sixVertexBoundaryReflectHorizontal_involutive {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :
    sixVertexBoundaryReflectHorizontal (sixVertexBoundaryReflectHorizontal ξ) = ξ := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexBoundaryReflectHorizontal]

@[simp] theorem sixVertexBoundaryReflectVertical_involutive {N M : ℕ}
    (ξ : SixVertexRectangleBoundary N M) :
    sixVertexBoundaryReflectVertical (sixVertexBoundaryReflectVertical ξ) = ξ := by
  apply SixVertexRectangleBoundary.ext <;> funext i <;>
    simp [sixVertexBoundaryReflectVertical]

theorem bool_toNat_add_not_toNat (b : Bool) :
    b.toNat + (!b).toNat = 1 := by
  cases b <;> decide

theorem sixVertexRectangleReflectHorizontal_localWeight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleReflectHorizontal ω).localWeight c v =
      ω.localWeight c (v.1.rev, v.2) := by
  rw [SixVertexRectangleArrows.localWeight, SixVertexRectangleArrows.localWeight]
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleReflectHorizontal, Fin.rev_castSucc, Fin.rev_succ, Bool.not_not]
  have hL := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.rev.castSucc, v.2))
  have hR := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.rev.succ, v.2))
  have hB := bool_toNat_add_not_toNat
    (ω.vertical (v.1.rev, v.2.castSucc))
  have hT := bool_toNat_add_not_toNat
    (ω.vertical (v.1.rev, v.2.succ))
  have hin :
      (ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.vertical (v.1.rev, v.2.castSucc)).toNat +
            (ω.vertical (v.1.rev, v.2.succ)).toNat = 2 ↔
        (ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (ω.vertical (v.1.rev, v.2.castSucc)).toNat +
            (!ω.vertical (v.1.rev, v.2.succ)).toNat = 2 := by omega
  have hc :
      ((ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat = 0 ∨
        (ω.horizontal (v.1.rev.succ, v.2)).toNat +
            (!ω.horizontal (v.1.rev.castSucc, v.2)).toNat = 2) ↔
      ((ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat = 0 ∨
        (ω.horizontal (v.1.rev.castSucc, v.2)).toNat +
            (!ω.horizontal (v.1.rev.succ, v.2)).toNat = 2) := by omega
  rw [if_congr hin (if_congr hc rfl rfl) rfl]
  split_ifs <;> rfl

theorem sixVertexRectangleReflectVertical_localWeight {N M : ℕ}
    (c : ℝ) (ω : SixVertexRectangleArrows N M) (v : Fin N × Fin M) :
    (sixVertexRectangleReflectVertical ω).localWeight c v =
      ω.localWeight c (v.1, v.2.rev) := by
  rw [SixVertexRectangleArrows.localWeight, SixVertexRectangleArrows.localWeight]
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexRectangleArrows.IsCType,
    sixVertexRectangleReflectVertical, Fin.rev_castSucc, Fin.rev_succ, Bool.not_not]
  have hL := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.castSucc, v.2.rev))
  have hR := bool_toNat_add_not_toNat
    (ω.horizontal (v.1.succ, v.2.rev))
  have hB := bool_toNat_add_not_toNat
    (ω.vertical (v.1, v.2.rev.castSucc))
  have hT := bool_toNat_add_not_toNat
    (ω.vertical (v.1, v.2.rev.succ))
  have hin :
      (!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat +
            (ω.vertical (v.1, v.2.rev.succ)).toNat +
            (!ω.vertical (v.1, v.2.rev.castSucc)).toNat = 2 ↔
        (ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat +
            (ω.vertical (v.1, v.2.rev.castSucc)).toNat +
            (!ω.vertical (v.1, v.2.rev.succ)).toNat = 2 := by omega
  have hc :
      ((!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat = 0 ∨
        (!ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (ω.horizontal (v.1.succ, v.2.rev)).toNat = 2) ↔
      ((ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat = 0 ∨
        (ω.horizontal (v.1.castSucc, v.2.rev)).toNat +
            (!ω.horizontal (v.1.succ, v.2.rev)).toNat = 2) := by omega
  rw [if_congr hin (if_congr hc rfl rfl) rfl]
  split_ifs <;> rfl

end StatMech.FrontierD
