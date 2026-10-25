/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Def.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part4
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorRow_rowInSector {N n : ℕ}
    (x : SixVertexRow N) (h : sixVertexUpCount x = n) :
    sixVertexSectorRow (sixVertexRowInSector x h) = x := by
  funext i
  simp [sixVertexSectorRow, sixVertexRowInSector]

theorem sixVertexPeriodicRows_upCount_eq {N M : ℕ} (hM : 0 < M) (c : ℝ)
    (x : SixVertexPeriodicRows N M hM c) (i : Fin M) :
    sixVertexUpCount (x.1 i) = sixVertexUpCount (x.1 ⟨0, hM⟩) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hM.ne'
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
      have hs : finitePeriodicSucc hM i.castSucc = i.succ := by
        ext
        simp [finitePeriodicSucc, Nat.mod_eq_of_lt]
      have hstep := sixVertexTransfer_preserves_upCount c (x.property i.castSucc)
      rw [hs] at hstep
      exact hstep.symm.trans ih

end StatMech.FrontierD
