/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexSeparation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexEnum.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexVertexBijection.Part5
import Def.StatisticalMechanics.Code.Universality.HexVertexSeparation.Part2


namespace StatMech.Universality

open Complex

open Function

open HexWalk

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


theorem hexSep_specialMidCount_congr (a : ℂ) (h0 : ℤ) (v du : ℂ) (ts ts' : List ℤ)
    (h : ts = ts') :
    specialMidCount a h0 v du ts = specialMidCount a h0 v du ts' := by
  rw [h]


theorem hexSep_passesThrough_r_of_count_three (ts : List ℤ)
    (hk : specialMidCount a h0 v du ts = 3) :
    PassesThrough a h0 ts (v + hexOmega ^ 2 * du) := by
  classical
  unfold specialMidCount at hk
  by_contra hc
  rw [if_neg hc] at hk
  have h1 : (if PassesThrough a h0 ts (v + du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  have h2 : (if PassesThrough a h0 ts (v + hexOmega * du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  omega


theorem hexSep_passesThrough_q_of_count_three (ts : List ℤ)
    (hk : specialMidCount a h0 v du ts = 3) :
    PassesThrough a h0 ts (v + hexOmega * du) := by
  classical
  unfold specialMidCount at hk
  by_contra hc
  rw [if_neg hc] at hk
  have h1 : (if PassesThrough a h0 ts (v + du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  have h3 : (if PassesThrough a h0 ts (v + hexOmega ^ 2 * du) then (1 : ℕ) else 0) ≤ 1 := by
    split <;> norm_num
  omega


theorem hexSep_neg_len_le_sum (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1) :
    -(L.length : ℤ) ≤ L.sum := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    have hy : y = 1 ∨ y = -1 := hL y (by simp)
    have hys : ∀ t ∈ ys, t = 1 ∨ t = -1 := fun t ht => hL t (by simp [ht])
    have hb := ih hys
    simp only [List.length_cons, List.sum_cons]
    push_cast; rcases hy with h | h <;> omega


theorem hexSep_legalSum_neg_four_len_ge (L : List ℤ) (hL : ∀ t ∈ L, t = 1 ∨ t = -1)
    (hsum : L.sum = -4) : 4 ≤ L.length := by
  have hb := hexSep_neg_len_le_sum L hL
  rw [hsum] at hb
  have : (4 : ℤ) ≤ (L.length : ℤ) := by omega
  exact_mod_cast this


theorem hexSep_pairLq_length_ge (E : HexVertexEnumeration region a h0 v du)
    (P : ℕ) (hP : P ∈ E.pairs) : 4 ≤ (E.pairLq P).length := by
  have hlegal := (E.pairQ_valid P hP).1.1
  unfold HexWalk.LegalTurns at hlegal
  simp only [ofTurns_turns] at hlegal
  exact hexSep_legalSum_neg_four_len_ge (E.pairLq P)
    (fun t ht => hlegal t (by simp [ht]))
    (E.pairLq_sum P hP)


end StatMech.Universality
