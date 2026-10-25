/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexFiniteTorus.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.LinearAlgebra.Matrix.Trace
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexFiniteTorus.Part3
open Finset Matrix


namespace StatMech.FrontierD

noncomputable def sixVertexPeriodicRowsLabelEquiv
    (N M : ℕ) (hM : 0 < M) (c : ℝ) :
    SixVertexPeriodicRows N M hM c ≃
      Σ n : Fin (N + 1), SixVertexPeriodicRowsInSector N M hM c n where
  toFun x := ⟨sixVertexPeriodicSectorIndex x, ⟨x, rfl⟩⟩
  invFun nx := nx.2.1
  left_inv _ := rfl
  right_inv nx := by
    rcases nx with ⟨n, ⟨x, hx⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      exact hx
    · apply (Subtype.heq_iff_coe_eq (fun y => by
          change (sixVertexUpCount (y.1 ⟨0, hM⟩) =
            (sixVertexPeriodicSectorIndex x).val) ↔
            (sixVertexUpCount (y.1 ⟨0, hM⟩) = n.val)
          rw [show (sixVertexPeriodicSectorIndex x).val = n.val from hx])).2
      rfl


noncomputable def sixVertexPeriodicRowsFixedSectorEquiv
    (N M : ℕ) (hM : 0 < M) (c : ℝ) (n : Fin (N + 1)) :
    SixVertexPeriodicRowsInSector N M hM c n ≃
      MatrixCompatibleCycle hM (sixVertexSectorTransfer N n c) where
  toFun x := by
    let y : Fin M → SixVertexSector N n := fun i =>
      sixVertexRowInSector (x.1.1 i)
        ((sixVertexPeriodicRows_upCount_eq hM c x.1 i).trans x.2)
    refine ⟨y, ?_⟩
    intro i
    change sixVertexTransfer N c (sixVertexSectorRow (y i))
      (sixVertexSectorRow (y (finitePeriodicSucc hM i))) ≠ 0
    simpa [y] using x.1.2 i
  invFun y := by
    refine ⟨⟨fun i => sixVertexSectorRow (y.1 i), ?_⟩, ?_⟩
    · intro i
      exact y.2 i
    · simp
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    simp
  right_inv y := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    ext j
    simp [sixVertexRowInSector, sixVertexSectorRow]

end StatMech.FrontierD
