/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc17arbitrary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Walls.rc16sliceunion
import Theorem.StatisticalMechanics.Code.Walls.rc9core.Part2
import Theorem.StatisticalMechanics.Code.Walls.rc8core.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterflyInjClose.Part2
import Def.StatisticalMechanics.Code.Walls.rc17arbitrary.Part4
open Finset MeasureTheory
open scoped FinsetFamily StatMech NNReal


namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]


theorem rc17_subset_upClosure {n : ℕ} (A : Set (ConfigSpace (Fin n))) : A ⊆ rc17_upClosure A :=
  fun ω hω => ⟨ω, hω, le_refl ω⟩


theorem rc17_upClosure_increasing {n : ℕ} (A : Set (ConfigSpace (Fin n))) :
    IsIncreasing (rc17_upClosure A) := by
  intro ω ω' hωω' hω
  obtain ⟨ω₀, hω₀, hle⟩ := hω
  exact ⟨ω₀, hω₀, hle.trans hωω'⟩


theorem rc17_box_subset_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    disjointOccurrence A B ⊆ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B) :=
  disjointOccurrence_mono (rc17_subset_upClosure A) (rc17_subset_upClosure B)

open Classical in


theorem rc17_box_le_reflInter_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
  have hbox : #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B))
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B))) := by
    apply Finset.card_le_card
    intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact rc17_box_subset_up A B hω
  have hdef : rc5_deficit (rc17_upClosure A) (rc17_upClosure B) ≤ 0 :=
    rc16_deficitBridgeIncInc n (rc17_upClosure A) (rc17_upClosure B)
      (rc17_upClosure_increasing A) (rc17_upClosure_increasing B)
  rw [rc5_deficit] at hdef
  have hbox' : (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ disjointOccurrence (rc17_upClosure A) (rc17_upClosure B))) := by exact_mod_cast hbox
  omega


theorem rc17_reflInter_subset_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    A ∩ rmr_reflect B ⊆ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B) := by
  rintro ω ⟨hA, hB⟩
  refine ⟨rc17_subset_upClosure A hA, ?_⟩
  rw [rmr_mem_reflect] at hB ⊢
  exact rc17_subset_upClosure B hB

open Classical in


theorem rc17_reflInter_card_le_up {n : ℕ} (A B : Set (ConfigSpace (Fin n))) :
    #(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ A ∩ rmr_reflect B))
      ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
            ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B))) := by
  apply Finset.card_le_card
  intro ω hω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
  exact rc17_reflInter_subset_up A B hω


open Classical in


theorem rc17_functional_bkr_of_reimer (h : ReimerWprobCore) {n : ℕ} {ι κ : Type*}
    (A : ι → Set (ConfigSpace (Fin n))) (B : κ → Set (ConfigSpace (Fin n)))
    (K : ι → Set (Fin n)) (L : κ → Set (Fin n))
    (hA : ∀ i, DependsOn (A i) (K i)) (hB : ∀ j, DependsOn (B j) (L j))
    (φ : Fin n → Bool → ℝ) (hφ0 : ∀ i b, 0 ≤ φ i b) (hφ1 : ∀ i, φ i false + φ i true = 1) :
    wprob φ {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ≤ wprob φ (⋃ i, A i) * wprob φ (⋃ j, B j) := by
  have hsub : {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ⊆ disjointOccurrence (⋃ i, A i) (⋃ j, B j) := by
    rintro ω ⟨i, j, hKL, hAi, hBj⟩
    refine ⟨K i, L j, hKL, ?_, ?_⟩
    · exact ((hA i).occursOn_iff ω |>.mpr hAi).mono_event (Set.subset_iUnion A i)
    · exact ((hB j).occursOn_iff ω |>.mpr hBj).mono_event (Set.subset_iUnion B j)
  calc wprob φ {ω | ∃ i j, Disjoint (K i) (L j) ∧ ω ∈ A i ∧ ω ∈ B j}
      ≤ wprob φ (disjointOccurrence (⋃ i, A i) (⋃ j, B j)) := wprob_mono hφ0 hsub
    _ ≤ wprob φ (⋃ i, A i) * wprob φ (⋃ j, B j) := h n φ hφ0 hφ1 _ _


set_option linter.unusedFintypeInType false in
set_option linter.unusedDecidableInType false in
open Classical in


theorem rc17_arbitrary_reimer :
    (∀ {n : ℕ} {A B : Set (ConfigSpace (Fin n))},
        (IsIncreasing A ∨ IsDecreasing A) → (IsIncreasing B ∨ IsDecreasing B) →
          rc5_deficit A B ≤ 0)
      ∧ (rc7_DeficitBridge ↔ rc17_NonMonotoneDeficit)
      ∧ (rc17_NonMonotoneDeficit → ReimerWprobCore)
      ∧ ¬ IsIncreasing (rc17_spreadEvent rbi_A)
      ∧ (∀ {n : ℕ} (A B : Set (ConfigSpace (Fin n))),
          (#(univ.filter (fun ω : ConfigSpace (Fin n) => ω ∈ disjointOccurrence A B)) : ℤ)
            ≤ #(univ.filter (fun ω : ConfigSpace (Fin n) =>
                  ω ∈ rc17_upClosure A ∩ rmr_reflect (rc17_upClosure B)))) :=
  ⟨fun {_ _ _} hA hB => rc17_deficit_le_zero_of_bothMonotone hA hB,
    rc17_deficitBridge_iff_nonMonotone,
    rc17_reimerWprobCore_of_nonMonotone,
    rc17_spread_not_increasing,
    fun {_} A B => rc17_box_le_reflInter_up A B⟩

end StatMech.Walls
