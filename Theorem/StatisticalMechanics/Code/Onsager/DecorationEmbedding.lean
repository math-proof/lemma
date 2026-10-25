/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding


namespace StatMech.Onsager

@[simp] theorem ons_decEmbedOffset_fst_le (mu : Fin 4) :
    (ons_decEmbedOffset mu).1 ≤ 6 := by
  fin_cases mu <;> decide

@[simp] theorem ons_decEmbedOffset_snd_le (mu : Fin 4) :
    (ons_decEmbedOffset mu).2 ≤ 6 := by
  fin_cases mu <;> decide

theorem ons_decEmbedCoord_lt (L : ℕ) [Fact (2 < L)]
    (z : ZMod L) (c : ℕ) (hc : c ≤ 6) :
    8 * z.val + c < 8 * L := by
  have hz := z.val_lt
  omega

@[simp] theorem ons_decEmbedVertex_fst_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    (ons_decEmbedVertex L d).1.val =
      8 * d.1.1.val + (ons_decEmbedOffset d.2).1 := by
  unfold ons_decEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt
    (ons_decEmbedCoord_lt L d.1.1 _ (ons_decEmbedOffset_fst_le d.2))

@[simp] theorem ons_decEmbedVertex_snd_val
    (L : ℕ) [Fact (2 < L)] (d : ons_Dart L) :
    (ons_decEmbedVertex L d).2.val =
      8 * d.1.2.val + (ons_decEmbedOffset d.2).2 := by
  unfold ons_decEmbedVertex
  rw [ZMod.val_natCast]
  exact Nat.mod_eq_of_lt
    (ons_decEmbedCoord_lt L d.1.2 _ (ons_decEmbedOffset_snd_le d.2))


theorem ons_decEmbedVertex_injective (L : ℕ) [Fact (2 < L)] :
    Function.Injective (ons_decEmbedVertex L) := by
  rintro ⟨⟨x, y⟩, mu⟩ ⟨⟨x', y'⟩, nu⟩ h
  have hx := congrArg (fun p => p.1.val) h
  have hy := congrArg (fun p => p.2.val) h
  simp only [ons_decEmbedVertex_fst_val, ons_decEmbedVertex_snd_val] at hx hy
  fin_cases mu <;> fin_cases nu <;>
    simp only [ons_decEmbedOffset] at hx hy ⊢
  all_goals
    have hxeq : x = x' := by
      apply ZMod.val_injective
      omega
    have hyeq : y = y' := by
      apply ZMod.val_injective
      omega
    simp [hxeq, hyeq] <;> omega


end StatMech.Onsager
