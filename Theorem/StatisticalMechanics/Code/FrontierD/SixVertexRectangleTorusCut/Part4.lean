/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexRectangleTorusCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexRectangleBoundary.Part3
import Def.StatisticalMechanics.Code.FrontierD.SixVertexRectangleTorusCut.Part4
open Finset


namespace StatMech.FrontierD

theorem cyclicPred_succ {N : ℕ} (i : Fin N) :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) i.succ = i.castSucc := by
  ext
  simp only [SixVertexArrows.cyclicPred, Fin.val_succ, Fin.val_castSucc]
  rw [show i.val + 1 + (N + 1) - 1 = (N + 1) + i.val by omega, Nat.add_mod_left,
    Nat.mod_eq_of_lt (i.isLt.trans (Nat.lt_succ_self N))]

theorem cyclicPred_zero {N : ℕ} :
    SixVertexArrows.cyclicPred (Nat.succ_pos N) (0 : Fin (N + 1)) = Fin.last N := by
  ext
  simp [SixVertexArrows.cyclicPred, Nat.mod_eq_of_lt]

theorem sixVertexCutTorusArrows_horizontal_castSucc
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).horizontal (i.castSucc, j) =
      ω.horizontal (SixVertexArrows.cyclicPred T.width_pos i, j) := by
  rcases T with ⟨W, H, hW, hH, eW, eH⟩
  obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hW.ne'
  have hlast : finLastOfPos hW = Fin.last N := by
    ext
    simp [finLastOfPos]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [sixVertexCutTorusArrows, cyclicPred_zero, hlast]
  · simp [sixVertexCutTorusArrows, cyclicPred_succ]

theorem sixVertexCutTorusArrows_vertical_castSucc
    (T : EvenTorus) (ω : SixVertexArrows T) (i : Fin T.width)
    (j : Fin T.height) :
    (sixVertexCutTorusArrows T ω).vertical (i, j.castSucc) =
      ω.vertical (i, SixVertexArrows.cyclicPred T.height_pos j) := by
  rcases T with ⟨W, H, hW, hH, eW, eH⟩
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hH.ne'
  have hlast : finLastOfPos hH = Fin.last M := by
    ext
    simp [finLastOfPos]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [sixVertexCutTorusArrows, cyclicPred_zero, hlast]
  · simp [sixVertexCutTorusArrows, cyclicPred_succ]

theorem sixVertexCutTorusArrows_incomingCount
    (T : EvenTorus) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).incomingCount v = ω.incomingCount v := by
  simp only [SixVertexRectangleArrows.incomingCount, SixVertexArrows.incomingCount,
    sixVertexCutTorusArrows_horizontal_castSucc,
    sixVertexCutTorusArrows_horizontal_succ,
    sixVertexCutTorusArrows_vertical_castSucc,
    sixVertexCutTorusArrows_vertical_succ]

theorem sixVertexCutTorusArrows_isCType
    (T : EvenTorus) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).IsCType v ↔ ω.IsCType v := by
  simp only [SixVertexRectangleArrows.IsCType, SixVertexArrows.IsCType,
    sixVertexCutTorusArrows_horizontal_castSucc,
    sixVertexCutTorusArrows_horizontal_succ]

theorem sixVertexCutTorusArrows_localWeight
    (T : EvenTorus) (c : ℝ) (ω : SixVertexArrows T) (v : T.Vertex) :
    (sixVertexCutTorusArrows T ω).localWeight c v = ω.localWeight c v := by
  classical
  rw [SixVertexRectangleArrows.localWeight, SixVertexArrows.localWeight,
    sixVertexCutTorusArrows_incomingCount]
  rw [if_congr (sixVertexCutTorusArrows_isCType T ω v) rfl rfl]

theorem sixVertexCutTorusArrows_weight
    (T : EvenTorus) (c : ℝ) (ω : SixVertexArrows T) :
    (sixVertexCutTorusArrows T ω).weight c = ω.weight c := by
  rw [SixVertexRectangleArrows.weight, SixVertexArrows.weight]
  apply Finset.prod_congr rfl
  intro v hv
  exact sixVertexCutTorusArrows_localWeight T c ω v


end StatMech.FrontierD
