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
import Def.StatisticalMechanics.Code.Universality.HexLiteralSubcritical.Part3


namespace StatMech.Universality

open HexWalk


theorem hls_encode_ne_allTrue (a : ℂ) (h0 : ℤ) (d : hls_ExactSAW a h0 6) :
    hls_encode a h0 6 d ≠ hls_allTrue := by
  intro henc
  have hturns : d.1 = List.replicate 6 (1 : ℤ) := by
    apply List.ext_get
    · simp [hls_exact_length a h0 6 d]
    · intro k hkd hkr
      have hk : k < 6 := by simpa [hls_exact_length a h0 6 d] using hkd
      have hbit := congrFun henc (⟨k, hk⟩ : Fin 6)
      have hone : d.1.get ⟨k, hkd⟩ = 1 := by
        apply of_decide_eq_true
        change hls_encode a h0 6 d ⟨k, hk⟩ = true
        simpa [hls_allTrue] using hbit
      rw [hone]
      exact (List.getElem_replicate hkr).symm
  have hsaw : (ofTurns a h0 d.1).IsSAW :=
    ((hlc_mem_sawFinset a h0 6 d.1).mp d.2).1.2
  rw [hturns] at hsaw
  have hclosed := hexJordan_six_left_not_saw a h0 [] []
  apply hclosed
  simpa [List.replicate_succ] using hsaw


theorem hls_encode_ne_allFalse (a : ℂ) (h0 : ℤ) (d : hls_ExactSAW a h0 6) :
    hls_encode a h0 6 d ≠ hls_allFalse := by
  intro henc
  have hturns : d.1 = List.replicate 6 (-1 : ℤ) := by
    apply List.ext_get
    · simp [hls_exact_length a h0 6 d]
    · intro k hkd hkr
      have hk : k < 6 := by simpa [hls_exact_length a h0 6 d] using hkd
      have hbit := congrFun henc (⟨k, hk⟩ : Fin 6)
      have hlegal : (ofTurns a h0 d.1).IsLegalSAW :=
        ((hlc_mem_sawFinset a h0 6 d.1).mp d.2).1
      have hchoice := hlegal.1 (d.1.get ⟨k, hkd⟩) (by
        simpa only [ofTurns_turns] using List.get_mem d.1 ⟨k, hkd⟩)
      have hnotOne : d.1.get ⟨k, hkd⟩ ≠ 1 := by
        intro hone
        have htrue : hls_encode a h0 6 d ⟨k, hk⟩ = true := by
          simp only [hls_encode, decide_eq_true_eq]
          simpa only using hone
        have hfalse : hls_allFalse ⟨k, hk⟩ = false := rfl
        rw [henc, hfalse] at htrue
        simp at htrue
      rcases hchoice with hone | hneg
      · exact (hnotOne hone).elim
      · rw [hneg]
        exact (List.getElem_replicate hkr).symm
  have hsaw : (ofTurns a h0 d.1).IsSAW :=
    ((hlc_mem_sawFinset a h0 6 d.1).mp d.2).1.2
  rw [hturns] at hsaw
  have hclosed := hexJordan_six_right_not_saw a h0 [] []
  apply hclosed
  simpa [List.replicate_succ] using hsaw


end StatMech.Universality
