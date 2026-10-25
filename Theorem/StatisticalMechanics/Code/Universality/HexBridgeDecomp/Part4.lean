/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part4


namespace StatMech.Universality

open List


theorem hexHW_lead_drop_append (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_leadRun p rest ++ hexHW_dropRun p rest = p :: rest := by
  simp [hexHW_leadRun, hexHW_dropRun, List.takeWhile_append_dropWhile]

theorem hexHW_dropRun_length_lt (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    (hexHW_dropRun p rest).length < (p :: rest).length := by
  have hkey : (hexHW_leadRun p rest).length + (hexHW_dropRun p rest).length
      = (p :: rest).length := by
    have := hexHW_lead_drop_append p rest
    calc (hexHW_leadRun p rest).length + (hexHW_dropRun p rest).length
        = (hexHW_leadRun p rest ++ hexHW_dropRun p rest).length := by
          rw [List.length_append]
      _ = (p :: rest).length := by rw [this]
  have hlead_pos : 0 < (hexHW_leadRun p rest).length := by
    have : p ∈ hexHW_leadRun p rest := by
      simp only [hexHW_leadRun]
      rw [List.takeWhile_cons]
      simp
    exact List.length_pos_of_mem this
  omega

theorem hexHW_leadRun_ne_nil (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_leadRun p rest ≠ [] := by
  simp only [hexHW_leadRun, ne_eq]
  rw [List.takeWhile_cons]; simp

theorem hexHW_leadRun_content_ne (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    (hexHW_leadRun p rest).map Prod.snd ≠ [] := by
  simp only [ne_eq, List.map_eq_nil_iff]
  exact hexHW_leadRun_ne_nil p rest

theorem hexHW_dropRun_sublist (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) :
    hexHW_dropRun p rest <+ p :: rest := by
  simp only [hexHW_dropRun]
  exact List.dropWhile_sublist _


theorem hexHW_leadRun_fst (p : ℕ × ℤ) (rest : List (ℕ × ℤ)) {q : ℕ × ℤ}
    (hq : q ∈ hexHW_leadRun p rest) : q.1 = p.1 := by
  simp only [hexHW_leadRun] at hq
  simpa using List.mem_takeWhile_imp hq


end StatMech.Universality
