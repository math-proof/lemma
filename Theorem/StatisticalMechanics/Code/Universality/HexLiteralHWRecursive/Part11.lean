/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWRecursive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWContent.Part12
import Theorem.StatisticalMechanics.Code.Universality.HexW2Summable.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Def.StatisticalMechanics.Code.Universality.HexLiteralHWRecursive.Part11


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


theorem hlhr_slice_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) {lo len : ℕ}
    (hbound : lo + len ≤ ts.length) :
    (ofTurns (hlhr_pieceMid a h0 ts lo) (hlhr_pieceHead h0 ts lo)
      ((ts.drop lo).take len)).IsLegalSAW := by
  have hlo : lo ≤ ts.length := by omega
  have hsuf := hexCut_legal_drop a h0 ts lo hlo hleg
  apply hexCut_legal_take _ _ (ts.drop lo) len hsuf


theorem hlhr_slice_legal_rebase (a a' : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) {lo len : ℕ}
    (hbound : lo + len ≤ ts.length) :
    (ofTurns a' (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)).IsLegalSAW := by
  have hs := hlhr_slice_legal a h0 ts hleg hbound
  have ht := hexW2S_isLegalSAW_translate
    (a' - hlhr_pieceMid a h0 ts lo) (hlhr_pieceMid a h0 ts lo)
    (hlhr_pieceHead h0 ts lo) ((ts.drop lo).take len)
  rw [add_sub_cancel] at ht
  exact ht.mpr hs


theorem hlhr_literalInterval_bounds (h0 : ℤ) (ts : List ℤ)
    (hhalf : HLHRLiteralHalfSpace h0 ts) :
    ∀ p ∈ hlhr_literalIntervals h0 ts,
      p.1 < p.2 ∧ p.2 ≤ ts.length := by
  intro p hp
  have hne : ts ≠ [] := by
    intro hempty
    simp [hlhr_literalIntervals, hempty, hlhr_intervalsAux] at hp
  have hlen : 0 < ts.length := List.length_pos_iff.mpr hne
  have hb := hlhr_intervalsAux_bounds (hlhr_height h0 ts) ts.length
    ts.length 0 true hlen (hlhr_literalHalfSpace_ahead h0 ts hhalf) p hp
  exact ⟨hb.2.1, hb.2.2⟩


theorem hlhr_literalInterval_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns (hlhr_pieceMid a h0 ts p.1) (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p)).IsLegalSAW := by
  obtain ⟨hp12, hp2len⟩ := hlhr_literalInterval_bounds h0 ts hhalf p hp
  unfold hlhr_intervalContent
  apply hlhr_slice_legal a h0 ts hleg
  omega


theorem hlhr_literalInterval_legal_rebase (a a' : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p)).IsLegalSAW := by
  obtain ⟨hp12, hp2len⟩ := hlhr_literalInterval_bounds h0 ts hhalf p hp
  unfold hlhr_intervalContent
  apply hlhr_slice_legal_rebase a a' h0 ts hleg
  omega


theorem hlhr_literalInterval_reflected_legal (a a' : ℂ) (h0 : ℤ)
    (ts : List ℤ) (hleg : (ofTurns a h0 ts).IsLegalSAW)
    (hhalf : HLHRLiteralHalfSpace h0 ts) {p : ℕ × ℕ}
    (hp : p ∈ hlhr_literalIntervals h0 ts) :
    (ofTurns a' (hlhr_pieceHead h0 ts p.1)
      (hsc_negTurns (hlhr_intervalContent ts p))).IsLegalSAW := by
  have hs := hlhr_literalInterval_legal_rebase a a' h0 ts hleg hhalf hp
  exact ⟨hsc_genLegalTurns a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p) hs.1,
    hsc_genIsSAW a' (hlhr_pieceHead h0 ts p.1)
      (hlhr_intervalContent ts p) hs.2⟩


end StatMech.Universality
