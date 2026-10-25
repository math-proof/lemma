/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexCoordinateBethe.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheScattering.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricProduct.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Mathlib.GroupTheory.Perm.Fin
import Def.StatisticalMechanics.Code.FrontierD.SixVertexCoordinateBethe.Part3
open Finset Matrix
open scoped symmDiff


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexSectorTransferComplex_apply
    (N n : ℕ) (c : ℝ) (x y : SixVertexSector N n) :
    sixVertexSectorTransferComplex N n c x y =
      (sixVertexSectorTransfer N n c x y : ℂ) := rfl

theorem sixVertexSectorTransferComplex_mulVec_apply
    (N n : ℕ) (c : ℝ) (v : SixVertexSector N n → ℂ)
    (x : SixVertexSector N n) :
    (sixVertexSectorTransferComplex N n c).mulVec v x =
      ∑ y, (sixVertexSectorTransfer N n c x y : ℂ) * v y := rfl

theorem sixVertexSectorRowDistance_eq_card_symmDiff
    {N n : ℕ} (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
      ((x : Finset (Fin N)) ∆ (y : Finset (Fin N))).card := by
  unfold sixVertexRowDistance
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_symmDiff]
  simp [sixVertexSectorRow]
  tauto

theorem sixVertexSectorRowDistance_eq_two_mul_sdiff
    {N n : ℕ} (x y : SixVertexSector N n) :
    sixVertexRowDistance (sixVertexSectorRow x) (sixVertexSectorRow y) =
      2 * ((x : Finset (Fin N)) \ (y : Finset (Fin N))).card := by
  rw [sixVertexSectorRowDistance_eq_card_symmDiff]
  change (((x : Finset (Fin N)) \ (y : Finset (Fin N))) ∪
    ((y : Finset (Fin N)) \ (x : Finset (Fin N)))).card = _
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_sdiff, Finset.card_sdiff, x.prop, y.prop]
    rw [Finset.inter_comm]
    omega
  · rw [Finset.disjoint_left]
    intro i hix hiy
    simp only [Finset.mem_sdiff] at hix hiy
    exact hix.2 hiy.1


theorem sixVertexSectorTransferComplex_mulVec_eq_interlacedSum
    (N n : ℕ) (c : ℝ) (v : SixVertexSector N n → ℂ)
    (x : SixVertexSector N n) :
    (sixVertexSectorTransferComplex N n c).mulVec v x =
      2 * v x +
        ∑ y ∈ (Finset.univ.erase x),
          if SixVertexInterlaced (sixVertexSectorRow x)
              (sixVertexSectorRow y) then
            (c : ℂ) ^ sixVertexRowDistance (sixVertexSectorRow x)
              (sixVertexSectorRow y) * v y
          else 0 := by
  rw [sixVertexSectorTransferComplex_mulVec_apply]
  have hxmem : x ∈ (Finset.univ : Finset (SixVertexSector N n)) :=
    Finset.mem_univ x
  rw [← Finset.sum_erase_add _ _ hxmem]
  have hdiag : (sixVertexSectorTransfer N n c x x : ℂ) * v x =
      2 * v x := by
    simp [sixVertexSectorTransfer, sixVertexTransfer]
  rw [hdiag]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro y hy
  have hyx : y ≠ x := (Finset.mem_erase.mp hy).1
  have hxy : sixVertexSectorRow x ≠ sixVertexSectorRow y := by
    intro hrow
    apply hyx
    apply Subtype.ext
    ext i
    have hi := congrFun hrow i
    simpa [sixVertexSectorRow] using hi.symm
  by_cases hinter : SixVertexInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y)
  · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hinter]
  · simp [sixVertexSectorTransfer, sixVertexTransfer, hxy, hinter]


end
end StatMech.FrontierD
