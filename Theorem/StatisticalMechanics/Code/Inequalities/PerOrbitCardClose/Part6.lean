/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/PerOrbitCardClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerSwapInjClose.Part3
import Def.StatisticalMechanics.Code.Inequalities.PerOrbitCardClose.Part6
open Finset MeasureTheory
open scoped NNReal FinsetFamily


namespace StatMech

open ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem poc_swapInjection_of_witnessInjection (A B : Set (ConfigSpace α))
    (h : poc_WitnessInjection A B) : r2k_SwapInjection A B := by
  obtain ⟨W, hinj⟩ := h
  refine ⟨poc_swapSel A B W, ?_, hinj⟩
  intro p hp
  have := poc_membership A B p.1 p.2 (W.wK p.1) (W.occA p.1 hp) (W.wL p.1) (W.occB p.1 hp)
    (W.disj p.1 hp)
  dsimp only [swapPair_fst, swapPair_snd, poc_swapSel] at this ⊢
  exact this


theorem poc_rbi_Bwit_FF (wL : Fin 2 → Bool)
    (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false false)) : wL 0 = true := by
  by_contra h
  have h0 : wL 0 = false := by cases hw : wL 0 with | false => rfl | true => exact absurd hw h
  have hmem := hB (rbi_cfg true false) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rfl)
  simp only [rbi_B, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


theorem poc_rbi_Bwit_FT (wL : Fin 2 → Bool)
    (hB : OccursOn rbi_B {a | wL a = true} (rbi_cfg false true)) (h0 : wL 0 = false) :
    wL 1 = true := by
  by_contra h
  have h1 : wL 1 = false := by cases hw : wL 1 with | false => rfl | true => exact absurd hw h
  have hmem := hB (rbi_cfg true false) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rw [show ((1 : Fin 2) = (⟨1, by omega⟩ : Fin 2)) from rfl] at h1
      exact absurd ha (by rw [h1]; simp))
  simp only [rbi_B, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


theorem poc_rbi_Awit_FF_one (wK : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false false)) (h0 : wK 0 = false) :
    wK 1 = true := by
  by_contra h
  have h1 : wK 1 = false := by cases hw : wK 1 with | false => rfl | true => exact absurd hw h
  have hmem := hA (rbi_cfg true true) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rw [show ((1 : Fin 2) = (⟨1, by omega⟩ : Fin 2)) from rfl] at h1
      exact absurd ha (by rw [h1]; simp))
  simp only [rbi_A, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


theorem poc_rbi_Awit_FT_zero (wK : Fin 2 → Bool)
    (hA : OccursOn rbi_A {a | wK a = true} (rbi_cfg false true)) : wK 0 = true := by
  by_contra h
  have h0 : wK 0 = false := by cases hw : wK 0 with | false => rfl | true => exact absurd hw h
  have hmem := hA (rbi_cfg true true) (by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha
    fin_cases a
    · rw [show ((0 : Fin 2) = (⟨0, by omega⟩ : Fin 2)) from rfl] at h0
      exact absurd ha (by rw [h0]; simp)
    · rfl)
  simp only [rbi_A, Set.mem_setOf_eq, rbi_cfg_zero, rbi_cfg_one] at hmem
  exact hmem (by simp)


end StatMech
