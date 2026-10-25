/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part6


namespace StatMech.Onsager

@[simp] theorem ons_decMicroVertex_fst_val
    (L : ℕ) [Fact (2 < L)] (z : ons_DecMicroPoint L) :
    (ons_decMicroVertex L z).1.val = 8 * z.cell.1.val + z.offsetX.val := by
  unfold ons_decMicroVertex
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.cell.1.val_lt
  have ho := z.offsetX.isLt
  omega

@[simp] theorem ons_decMicroVertex_snd_val
    (L : ℕ) [Fact (2 < L)] (z : ons_DecMicroPoint L) :
    (ons_decMicroVertex L z).2.val = 8 * z.cell.2.val + z.offsetY.val := by
  unfold ons_decMicroVertex
  rw [ZMod.val_natCast]
  apply Nat.mod_eq_of_lt
  have hz := z.cell.2.val_lt
  have ho := z.offsetY.isLt
  omega

theorem ons_decMicroVertex_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_decMicroVertex L) := by
  intro z w h
  have hx := congrArg (fun p => p.1.val) h
  have hy := congrArg (fun p => p.2.val) h
  simp only [ons_decMicroVertex_fst_val] at hx
  simp only [ons_decMicroVertex_snd_val] at hy
  have hcx : z.cell.1 = w.cell.1 := by
    apply ZMod.val_injective
    omega
  have hcy : z.cell.2 = w.cell.2 := by
    apply ZMod.val_injective
    omega
  have hox : z.offsetX = w.offsetX := by
    apply Fin.ext
    omega
  have hoy : z.offsetY = w.offsetY := by
    apply Fin.ext
    omega
  have hc : z.cell = w.cell := Prod.ext hcx hcy
  cases z
  cases w
  simp_all


end StatMech.Onsager
