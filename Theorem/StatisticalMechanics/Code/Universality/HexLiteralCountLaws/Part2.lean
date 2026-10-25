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
import Def.StatisticalMechanics.Code.Universality.HexLiteralCountLaws.Part2


namespace StatMech.Universality

open HexWalk


@[simp]
theorem hlc_length_zigzagTurnsAux (phase : Bool) (n : ℕ) :
    (hlc_zigzagTurnsAux phase n).length = n := by
  induction n generalizing phase with
  | zero => cases phase <;> rfl
  | succ n ih => cases phase <;> simp [hlc_zigzagTurnsAux, ih]

@[simp]
theorem hlc_length_zigzagTurns (n : ℕ) : (hlc_zigzagTurns n).length = n := by
  simp [hlc_zigzagTurns]


theorem hlc_zigzagTurns_legal (phase : Bool) (n : ℕ) :
    ∀ t ∈ hlc_zigzagTurnsAux phase n, t = 1 ∨ t = -1 := by
  induction n generalizing phase with
  | zero => cases phase <;> simp [hlc_zigzagTurnsAux]
  | succ n ih =>
      cases phase with
      | false =>
          intro t ht
          simp only [hlc_zigzagTurnsAux, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact Or.inr rfl
          · exact ih true t ht
      | true =>
          intro t ht
          simp only [hlc_zigzagTurnsAux, List.mem_cons] at ht
          rcases ht with rfl | ht
          · exact Or.inl rfl
          · exact ih false t ht


theorem hlc_halfStep_zero_re_pos : 0 < (halfStep 0).re := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 by norm_num,
    Real.cos_pi_div_six]
  positivity

theorem hlc_halfStep_neg_one_re_pos : 0 < (halfStep (-1)).re := by
  rw [hexWall3_halfStep_re]
  rw [show Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) by
      push_cast; ring,
    Real.cos_neg, Real.cos_pi_div_six]
  positivity


theorem hlc_isChain_cons_verticesAux (x m : ℂ) (h : ℤ) (ts : List ℤ)
    (hstep : x.re < (m + halfStep h).re)
    (htail : List.IsChain (fun z w : ℂ => z.re < w.re) (verticesAux m h ts)) :
    List.IsChain (fun z w : ℂ => z.re < w.re) (x :: verticesAux m h ts) := by
  cases ts with
  | nil => exact .cons_cons hstep htail
  | cons t ts => exact .cons_cons hstep htail


theorem hlc_zigzag_vertices_chain (n : ℕ) :
    (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re)
      (verticesAux m 0 (hlc_zigzagTurnsAux false n))) ∧
    (∀ m : ℂ, List.IsChain (fun z w : ℂ => z.re < w.re)
      (verticesAux m (-1) (hlc_zigzagTurnsAux true n))) := by
  induction n with
  | zero =>
      constructor <;> intro m <;> exact .singleton _
  | succ n ih =>
      constructor
      · intro m
        rw [show hlc_zigzagTurnsAux false (n + 1) =
            -1 :: hlc_zigzagTurnsAux true n by rfl, verticesAux_cons]
        apply hlc_isChain_cons_verticesAux
        · simp only [Complex.add_re]
          have hp := hlc_halfStep_neg_one_re_pos
          norm_num at hp ⊢
          linarith
        · simpa using ih.2 (m + halfStep 0 + halfStep (0 + (-1)))
      · intro m
        rw [show hlc_zigzagTurnsAux true (n + 1) =
            1 :: hlc_zigzagTurnsAux false n by rfl, verticesAux_cons]
        apply hlc_isChain_cons_verticesAux
        · simp only [Complex.add_re]
          have hp := hlc_halfStep_zero_re_pos
          norm_num at hp ⊢
          linarith
        · simpa using ih.1 (m + halfStep (-1) + halfStep (-1 + 1))


theorem hlc_zigzag_isLegalSAW_zero (a : ℂ) (n : ℕ) :
    (ofTurns a 0 (hlc_zigzagTurns n)).IsLegalSAW := by
  constructor
  · simpa [LegalTurns, hlc_zigzagTurns] using hlc_zigzagTurns_legal false n
  · unfold IsSAW vertices ofTurns
    have hchain := (hlc_zigzag_vertices_chain n).1 a
    exact hchain.pairwise.imp
      (fun hlt heq => (ne_of_lt hlt) (congrArg Complex.re heq))


theorem hlc_zigzag_isLegalSAW (a : ℂ) (h0 : ℤ) (n : ℕ) :
    (ofTurns a h0 (hlc_zigzagTurns n)).IsLegalSAW := by
  exact (hhe_isLegalSAW_rebase a a 0 h0 (hlc_zigzagTurns n)).mpr
    (hlc_zigzag_isLegalSAW_zero a n)


theorem hlc_one_le_sawCount (a : ℂ) (h0 : ℤ) (n : ℕ) :
    1 ≤ hlc_sawCount a h0 n := by
  classical
  unfold hlc_sawCount hzc_sawCount
  apply Finset.one_le_card.mpr
  refine ⟨hlc_zigzagTurns n, ?_⟩
  simp only [Finset.mem_filter]
  constructor
  · rw [hzc_mem_truncFinset]
    refine ⟨hlc_zigzag_isLegalSAW a h0 n, ?_⟩
    simp [numVertices]
  · simp [numVertices]

theorem hlc_one_le_sawCountR (a : ℂ) (h0 : ℤ) (n : ℕ) :
    1 ≤ hlc_sawCountR a h0 n := by
  unfold hlc_sawCountR
  exact_mod_cast hlc_one_le_sawCount a h0 n


end StatMech.Universality
