/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCountLaws.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexZConvClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3


namespace StatMech.Universality

open HexWalk


@[simp]
theorem hlc_card_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) :
    (hlc_sawFinset a h0 n).card = hlc_sawCount a h0 n := by
  unfold hlc_sawFinset hlc_sawCount
  exact hzc_filterCard_eq a h0 (n + 2) (n + 1) (by omega)


theorem hlc_mem_sawFinset (a : ℂ) (h0 : ℤ) (n : ℕ) (ts : List ℤ) :
    ts ∈ hlc_sawFinset a h0 n ↔
      (ofTurns a h0 ts).IsLegalSAW ∧ ts.length = n := by
  simp only [hlc_sawFinset, Finset.mem_filter, hzc_mem_truncFinset]
  constructor
  · rintro ⟨⟨hleg, _⟩, hnum⟩
    refine ⟨hleg, ?_⟩
    simpa [numVertices] using hnum
  · rintro ⟨hleg, hlen⟩
    refine ⟨⟨hleg, ?_⟩, ?_⟩ <;> simp [numVertices, hlen]


theorem hlc_split_mem (a : ℂ) (h0 : ℤ) (m n : ℕ) {ts : List ℤ}
    (hts : ts ∈ hlc_sawFinset a h0 (m + n)) :
    (ts.take m, ts.drop m) ∈
      hlc_sawFinset a h0 m ×ˢ hlc_sawFinset a h0 n := by
  rw [Finset.mem_product]
  have hdata := (hlc_mem_sawFinset a h0 (m + n) ts).mp hts
  have hcp : m ≤ ts.length := by omega
  constructor
  · rw [hlc_mem_sawFinset]
    exact ⟨hexCut_legal_take a h0 ts m hdata.1, by simp [hdata.2]⟩
  · rw [hlc_mem_sawFinset]
    refine ⟨?_, by simp [List.length_drop, hdata.2]⟩
    have hdrop := hexCut_legal_drop a h0 ts m hcp hdata.1
    exact (hhe_isLegalSAW_rebase a (hexDropMid a h0 ts m) h0
      (h0 + (ts.take m).sum) (ts.drop m)).mp hdrop


theorem hlc_split_injective (m : ℕ) :
    Function.Injective (fun ts : List ℤ => (ts.take m, ts.drop m)) := by
  intro s t h
  have htake : s.take m = t.take m := congrArg Prod.fst h
  have hdrop : s.drop m = t.drop m := congrArg Prod.snd h
  calc
    s = s.take m ++ s.drop m := (List.take_append_drop m s).symm
    _ = t.take m ++ t.drop m := by rw [htake, hdrop]
    _ = t := List.take_append_drop m t


theorem hlc_sawCount_submult (a : ℂ) (h0 : ℤ) (m n : ℕ) :
    hlc_sawCount a h0 (m + n) ≤ hlc_sawCount a h0 m * hlc_sawCount a h0 n := by
  classical
  rw [← hlc_card_sawFinset a h0 (m + n), ← hlc_card_sawFinset a h0 m,
    ← hlc_card_sawFinset a h0 n, ← Finset.card_product]
  exact Finset.card_le_card_of_injOn
    (fun ts => (ts.take m, ts.drop m))
    (fun _ hts => hlc_split_mem a h0 m n hts)
    (fun _ _ _ _ h => hlc_split_injective m h)


theorem hlc_sawCountR_submultiplicative (a : ℂ) (h0 : ℤ) :
    Submultiplicative (hlc_sawCountR a h0) := by
  intro m n
  unfold hlc_sawCountR
  exact_mod_cast hlc_sawCount_submult a h0 m n


theorem hlc_sawFinset_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawFinset a' h0' n = hlc_sawFinset a h0 n := by
  ext ts
  rw [hlc_mem_sawFinset, hlc_mem_sawFinset]
  exact and_congr (hhe_isLegalSAW_rebase a a' h0 h0' ts) Iff.rfl


theorem hlc_sawCount_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawCount a' h0' n = hlc_sawCount a h0 n := by
  rw [← hlc_card_sawFinset, ← hlc_card_sawFinset,
    hlc_sawFinset_rebase a a' h0 h0' n]


theorem hlc_sawCountR_rebase (a a' : ℂ) (h0 h0' : ℤ) (n : ℕ) :
    hlc_sawCountR a' h0' n = hlc_sawCountR a h0 n := by
  simp only [hlc_sawCountR, hlc_sawCount_rebase a a' h0 h0' n]

end StatMech.Universality
