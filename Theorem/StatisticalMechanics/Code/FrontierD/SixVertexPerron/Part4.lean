/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Def.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part3
open Finset Matrix


namespace StatMech.FrontierD

@[simp] theorem sixVertexSectorPosition_lower {N n : ℕ} (x : SixVertexSector N n) :
    sixVertexSectorPosition (sixVertexLowerSector x) =
      lowerSectorEmbedding (sixVertexSectorPosition x) := by
  change Set.powersetCard.ofFinEmbEquiv.symm
      (Set.powersetCard.ofFinEmbEquiv (lowerSectorEmbedding (sixVertexSectorPosition x))) = _
  exact Equiv.symm_apply_apply _ _

theorem sixVertexLower_positionsForwardInterlaced {N n : ℕ}
    (x : SixVertexSector N n) :
    SixVertexPositionsForwardInterlaced (sixVertexLowerSector x) x := by
  constructor
  · intro i
    rw [sixVertexSectorPosition_lower]
    change (lowerSectorEmbedding (sixVertexSectorPosition x) i).val ≤
      (sixVertexSectorPosition x i).val
    simp only [lowerSectorEmbedding, OrderEmbedding.coe_ofStrictMono]
    apply max_le
    · exact fin_val_le_of_strictMono _ (sixVertexSectorPosition x).strictMono i
    · exact Nat.sub_le _ _
  · intro k hk
    rw [sixVertexSectorPosition_lower]
    change (sixVertexSectorPosition x ⟨k, by omega⟩).val ≤
      (lowerSectorEmbedding (sixVertexSectorPosition x) ⟨k + 1, hk⟩).val
    simp only [lowerSectorEmbedding, OrderEmbedding.coe_ofStrictMono]
    apply le_max_of_le_right
    have hmono :
        (sixVertexSectorPosition x ⟨k, by omega⟩).val <
          (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
      exact_mod_cast (sixVertexSectorPosition x).strictMono (by simp)
    omega

theorem sixVertexLower_interlaced {N n : ℕ} (x : SixVertexSector N n) :
    SixVertexInterlaced (sixVertexSectorRow (sixVertexLowerSector x))
      (sixVertexSectorRow x) :=
  Or.inl (sixVertexForwardInterlaced_of_positions _ _
    (sixVertexLower_positionsForwardInterlaced x))

theorem sixVertexSectorTransfer_lower_pos {N n : ℕ} {c : ℝ} (hc : 0 < c)
    (x : SixVertexSector N n) :
    0 < sixVertexSectorTransfer N n c (sixVertexLowerSector x) x := by
  classical
  by_cases h : sixVertexLowerSector x = x
  · simp [sixVertexSectorTransfer, sixVertexTransfer, h]
  · have hrow : sixVertexSectorRow (sixVertexLowerSector x) ≠ sixVertexSectorRow x := by
      intro heq
      apply h
      apply Subtype.ext
      ext i
      have hi := congrFun heq i
      simp only [sixVertexSectorRow_apply] at hi
      simpa using hi
    simp [sixVertexSectorTransfer, sixVertexTransfer, hrow, sixVertexLower_interlaced x,
      pow_pos hc]


end StatMech.FrontierD
