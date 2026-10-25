/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexFiniteStripClose


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


theorem hfs_verticesAux_take (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) :
    verticesAux m h (ts.take cp) = (verticesAux m h ts).take (cp + 1) := by
  induction ts generalizing m h cp with
  | nil => simp [verticesAux]
  | cons t ts ih =>
    cases cp with
    | zero => simp [verticesAux]
    | succ k =>
      rw [List.take_succ_cons, verticesAux_cons, verticesAux_cons, List.take_succ_cons]
      congr 1
      exact ih _ _ k


theorem hfs_verticesAux_drop (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) :
    verticesAux (hfs_stMid m h (ts.take cp)) (hfs_stHead h (ts.take cp)) (ts.drop cp)
      = (verticesAux m h ts).drop cp := by
  induction ts generalizing m h cp with
  | nil => simp_all [hfs_stMid, hfs_stHead]
  | cons t ts ih =>
    cases cp with
    | zero => simp [hfs_stMid, hfs_stHead, verticesAux]
    | succ k =>
      simp only [List.take_succ_cons, List.drop_succ_cons, hfs_stMid, hfs_stHead,
        verticesAux_cons]
      apply ih
      simp only [List.length_cons] at hcp
      omega


theorem hfs_legalTurns_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).LegalTurns) :
    (ofTurns a h0 (ts.take cp)).LegalTurns := by
  unfold LegalTurns at hleg ⊢
  intro t ht
  simp only [ofTurns_turns] at ht ⊢
  exact hleg t (List.mem_of_mem_take ht)


theorem hfs_legalTurns_drop (a2 : ℂ) (h2 : ℤ) (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).LegalTurns) :
    (ofTurns a2 h2 (ts.drop cp)).LegalTurns := by
  unfold LegalTurns at hleg ⊢
  intro t ht
  simp only [ofTurns_turns] at ht ⊢
  exact hleg t (List.mem_of_mem_drop ht)


theorem hfs_isSAW_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (h : (ofTurns a h0 ts).IsSAW) :
    (ofTurns a h0 (ts.take cp)).IsSAW := by
  unfold IsSAW vertices at h ⊢
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns] at h ⊢
  rw [hfs_verticesAux_take]
  exact h.take


theorem hfs_isSAW_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length)
    (h : (ofTurns a h0 ts).IsSAW) :
    (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).IsSAW := by
  unfold IsSAW vertices at h ⊢
  simp only [ofTurns_startMid, ofTurns_h0, ofTurns_turns] at h ⊢
  rw [hfs_verticesAux_drop a h0 ts cp hcp]
  exact h.drop


theorem hfs_isLegalSAW_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (h : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 (ts.take cp)).IsLegalSAW :=
  ⟨hfs_legalTurns_take a h0 ts cp h.1, hfs_isSAW_take a h0 ts cp h.2⟩


theorem hfs_isLegalSAW_drop (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hcp : cp ≤ ts.length) (h : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns (hfs_stMid a h0 (ts.take cp)) (hfs_stHead h0 (ts.take cp))
      (ts.drop cp)).IsLegalSAW :=
  ⟨hfs_legalTurns_drop _ _ a h0 ts cp h.1, hfs_isSAW_drop a h0 ts cp hcp h.2⟩


end StatMech.Universality
