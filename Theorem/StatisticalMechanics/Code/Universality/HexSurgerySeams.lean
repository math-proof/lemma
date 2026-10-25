/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexSurgerySeams.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3


namespace StatMech.Universality

open Complex HexWalk List Filter

open scoped Topology BigOperators


theorem hexVerticesAux_take_prefix (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) :
    (verticesAux m h (ts.take cp)) <+: (verticesAux m h ts) := by
  induction ts generalizing m h cp with
  | nil => simp
  | cons t ts ih =>
    cases cp with
    | zero =>
      simp only [List.take_zero, verticesAux_nil, verticesAux_cons]
      exact ⟨_, rfl⟩
    | succ cp =>
      simp only [List.take_succ_cons, verticesAux_cons]
      exact (prefix_cons_inj _).mpr (ih (m + halfStep h + halfStep (h + t)) (h + t) cp)


theorem hexVerticesAux_drop (m : ℂ) (h : ℤ) (ts : List ℤ) (cp : ℕ) (hcp : cp ≤ ts.length) :
    ∃ m', (verticesAux m h ts).drop cp = verticesAux m' (h + (ts.take cp).sum) (ts.drop cp) := by
  induction cp generalizing m h ts with
  | zero => exact ⟨m, by simp⟩
  | succ cp ih =>
    cases ts with
    | nil => simp at hcp
    | cons t ts =>
      simp only [List.length_cons] at hcp
      obtain ⟨m', hm'⟩ := ih (m + halfStep h + halfStep (h + t)) (h + t) ts (by omega)
      refine ⟨m', ?_⟩
      simp only [verticesAux_cons, List.drop_succ_cons, List.take_succ_cons, List.sum_cons]
      rw [hm', show h + (t + (ts.take cp).sum) = h + t + (ts.take cp).sum from by ring]


theorem hexCut_legal_take (a : ℂ) (h0 : ℤ) (ts : List ℤ) (cp : ℕ)
    (hleg : (ofTurns a h0 ts).IsLegalSAW) :
    (ofTurns a h0 (ts.take cp)).IsLegalSAW := by
  obtain ⟨hturns, hsaw⟩ := hleg
  refine ⟨fun t ht => hturns t (List.mem_of_mem_take ht), ?_⟩
  unfold IsSAW vertices ofTurns at hsaw ⊢
  simp only at hsaw ⊢
  exact hsaw.sublist (hexVerticesAux_take_prefix a h0 ts cp).sublist


end StatMech.Universality
