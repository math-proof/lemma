/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Instance.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorTransferComplex_eq_oriented
    (N m : Nat) (c : Real) (x y : SixVertexSector N m) :
    sixVertexSectorTransferComplex N m c x y =
      (if SixVertexForwardInterlaced (sixVertexSectorRow y)
          (sixVertexSectorRow x) then
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) else 0) +
      (if SixVertexForwardInterlaced (sixVertexSectorRow x)
          (sixVertexSectorRow y) then
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) else 0) := by
  classical
  by_cases hyx : SixVertexForwardInterlaced (sixVertexSectorRow y)
      (sixVertexSectorRow x)
  · by_cases hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have heq := sixVertexForwardInterlaced_antisymm x y hxy hyx
      subst y
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, sixVertexForwardInterlaced_refl,
        sixVertexRowDistance]
      norm_num
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hxy (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]
  · by_cases hxy : SixVertexForwardInterlaced (sixVertexSectorRow x)
        (sixVertexSectorRow y)
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hyx (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]
    · have hne : x ≠ y := by
        intro heq
        subst y
        exact hyx (sixVertexForwardInterlaced_refl x)
      have hrow : sixVertexSectorRow x ≠ sixVertexSectorRow y :=
        fun h => hne (sixVertexSectorRow_injective h)
      simp [sixVertexSectorTransferComplex, sixVertexSectorTransfer,
        sixVertexTransfer, hyx, hxy, hrow, SixVertexInterlaced]

theorem sixVertexSectorTransferComplex_mulVec_oriented
    (N m : Nat) (c : Real) (v : SixVertexSector N m -> Complex)
    (x : SixVertexSector N m) :
    (sixVertexSectorTransferComplex N m c).mulVec v x =
      (∑ y ∈ (Finset.univ : Finset (SixVertexSector N m)).filter
          (fun y => SixVertexForwardInterlaced
            (sixVertexSectorRow y) (sixVertexSectorRow x)),
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) * v y) +
      (∑ y ∈ (Finset.univ : Finset (SixVertexSector N m)).filter
          (fun y => SixVertexForwardInterlaced
            (sixVertexSectorRow x) (sixVertexSectorRow y)),
        (c : Complex) ^ sixVertexRowDistance
          (sixVertexSectorRow x) (sixVertexSectorRow y) * v y) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  simp_rw [sixVertexSectorTransferComplex_eq_oriented, add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hyx : SixVertexForwardInterlaced
        (sixVertexSectorRow y) (sixVertexSectorRow x) <;>
      simp [hyx, add_mul]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : SixVertexForwardInterlaced
        (sixVertexSectorRow x) (sixVertexSectorRow y) <;>
      simp [hxy, add_mul]

end
end StatMech.FrontierD
