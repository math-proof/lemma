/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationEdgeComponent
import Def.StatisticalMechanics.Code.Onsager.DecorationEmbedding.Part2


namespace StatMech.Onsager

theorem ons_eight_zmodCast_add_one
    (L : ℕ) [Fact (2 < L)] (z : ZMod L) :
    (8 : ZMod (8 * L)) * ZMod.cast z + 8 =
      8 * ZMod.cast (z + 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = -1
  · rw [hz, neg_add_cancel, ZMod.cast_zero, mul_zero]
    rw [ZMod.cast_eq_val, ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) = 0 := by
      calc
        (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) =
            ((8 : ℕ) : ZMod (8 * L)) * (L : ZMod (8 * L)) := by norm_num
        _ = ((8 * L : ℕ) : ZMod (8 * L)) := (Nat.cast_mul 8 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination hmod
  · have hv : z.val + 1 < L := by
      have hne : z.val ≠ L - 1 := by
        intro h
        apply hz
        apply ZMod.val_injective
        rw [h, ons_zmod_val_neg_one]
      have hzlt := z.val_lt
      omega
    have hval : (z + 1).val = z.val + 1 := by
      rw [ZMod.val_add, ZMod.val_one, Nat.mod_eq_of_lt hv]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    ring

theorem ons_eight_zmodCast_sub_one
    (L : ℕ) [Fact (2 < L)] (z : ZMod L) :
    (8 : ZMod (8 * L)) * ZMod.cast z - 8 =
      8 * ZMod.cast (z - 1) := by
  letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
  have hL : 1 ≤ L := by have := (Fact.out : 2 < L); omega
  by_cases hz : z = 0
  · rw [hz, zero_sub, ZMod.cast_zero, mul_zero, zero_sub]
    rw [ZMod.cast_eq_val, ons_zmod_val_neg_one]
    push_cast
    rw [Nat.cast_sub hL]
    have hmod : (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) = 0 := by
      calc
        (8 : ZMod (8 * L)) * (L : ZMod (8 * L)) =
            ((8 : ℕ) : ZMod (8 * L)) * (L : ZMod (8 * L)) := by norm_num
        _ = ((8 * L : ℕ) : ZMod (8 * L)) := (Nat.cast_mul 8 L).symm
        _ = 0 := ZMod.natCast_self _
    linear_combination -hmod
  · have hzval : 1 ≤ z.val := by
      have : z.val ≠ 0 := by
        intro h
        exact hz ((ZMod.val_eq_zero z).mp h)
      omega
    have hval : (z - 1).val = z.val - 1 := by
      have hone : (1 : ZMod L).val ≤ z.val := by
        rw [ZMod.val_one]
        exact hzval
      rw [ZMod.val_sub hone, ZMod.val_one]
    rw [ZMod.cast_eq_val, ZMod.cast_eq_val, hval]
    push_cast
    rw [Nat.cast_sub hzval]
    ring


theorem ons_decEdgeRoute_endpoint
    (L : ℕ) [Fact (2 < L)] (d e : ons_Dart L)
    (hde : (ons_decGraph L).Adj d e) :
    ons_fourDirSteps (8 * L) (ons_decEdgeRouteDirs L d e)
        (ons_decEmbedVertex L d) =
      ons_decEmbedVertex L e := by
  change ons_decAdj L d e at hde
  rcases hde with hrev | hint
  · subst e
    rcases d with ⟨⟨x, y⟩, mu⟩
    fin_cases mu <;>
      simp [ons_decEdgeRouteDirs, ons_fourDirSteps, ons_decEmbedVertex,
        ons_decEmbedOffset, ons_dartRev, ons_dirStep] <;>
      first
      | linear_combination ons_eight_zmodCast_add_one L x
      | linear_combination ons_eight_zmodCast_add_one L y
      | linear_combination ons_eight_zmodCast_sub_one L x
      | linear_combination ons_eight_zmodCast_sub_one L y
  · rcases d with ⟨p, mu⟩
    rcases e with ⟨q, nu⟩
    have hpq : p = q := hint.1
    subst q
    fin_cases mu <;> fin_cases nu <;>
      simp [ons_decInternalAdj, ons_decEdgeRouteDirs, ons_fourDirSteps,
        ons_decEmbedVertex, ons_decEmbedOffset, ons_dartRev, ons_dirStep] at hint ⊢ <;>
      ring_nf <;> simp


theorem ons_torusAdj_dirStep (N : ℕ) [Fact (2 < N)]
    (p : ZMod N × ZMod N) (mu : Fin 4) :
    (onsTorusGraph N).Adj p (ons_dirStep N mu p) := by
  rcases p with ⟨x, y⟩
  fin_cases mu <;> simp [onsTorusGraph, onsTorusAdj, ons_dirStep] <;> ring


end StatMech.Onsager
