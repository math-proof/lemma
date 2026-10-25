/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralSubcritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Def.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part2


namespace StatMech.Universality

open HexWalk


theorem hls_encode_injective (a : ℂ) (h0 : ℤ) (n : ℕ) :
    Function.Injective (hls_encode a h0 n) := by
  intro d e hde
  apply Subtype.ext
  apply List.ext_get
  · rw [hls_exact_length a h0 n d, hls_exact_length a h0 n e]
  · intro k hkd hke
    have hk : k < n := by simpa [hls_exact_length a h0 n d] using hkd
    have hbit := congrFun hde (⟨k, hk⟩ : Fin n)
    have hdlegal : (ofTurns a h0 d.1).IsLegalSAW :=
      ((hlc_mem_sawFinset a h0 n d.1).mp d.2).1
    have helegal : (ofTurns a h0 e.1).IsLegalSAW :=
      ((hlc_mem_sawFinset a h0 n e.1).mp e.2).1
    have hdturn := hdlegal.1 (d.1.get ⟨k, hkd⟩) (by
      simpa only [ofTurns_turns] using List.get_mem d.1 ⟨k, hkd⟩)
    have heturn := helegal.1 (e.1.get ⟨k, hke⟩) (by
      simpa only [ofTurns_turns] using List.get_mem e.1 ⟨k, hke⟩)
    rcases hdturn with hdturn | hdturn <;>
      rcases heturn with heturn | heturn
    · exact hdturn.trans heturn.symm
    · exfalso
      have hdenc : hls_encode a h0 n d ⟨k, hk⟩ = true := by
        simp only [hls_encode, decide_eq_true_eq]
        simpa only using hdturn
      have heenc : hls_encode a h0 n e ⟨k, hk⟩ = false := by
        rw [hls_encode, decide_eq_false_iff_not]
        intro heq
        have heq' : e.1.get ⟨k, hke⟩ = 1 := by simpa only using heq
        omega
      rw [hdenc, heenc] at hbit
      simp at hbit
    · exfalso
      have hdenc : hls_encode a h0 n d ⟨k, hk⟩ = false := by
        rw [hls_encode, decide_eq_false_iff_not]
        intro hdeq
        have hdeq' : d.1.get ⟨k, hkd⟩ = 1 := by simpa only using hdeq
        omega
      have heenc : hls_encode a h0 n e ⟨k, hk⟩ = true := by
        simp only [hls_encode, decide_eq_true_eq]
        simpa only using heturn
      rw [hdenc, heenc] at hbit
      simp at hbit
    · exact hdturn.trans heturn.symm


theorem hlc_sawCount_le_two_pow (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hlc_sawCount a h0 n ≤ 2 ^ n := by
  have hcard := Fintype.card_le_of_injective (hls_encode a h0 n)
    (hls_encode_injective a h0 n)
  simpa [hls_ExactSAW, hlc_card_sawFinset, Fintype.card_fun] using hcard


theorem hlc_sawCountR_le_two_pow (a : ℂ) (h0 : ℤ) (n : ℕ) :
    hlc_sawCountR a h0 n ≤ (2 : ℝ) ^ n := by
  unfold hlc_sawCountR
  exact_mod_cast hlc_sawCount_le_two_pow a h0 n


end StatMech.Universality
