/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerButterflyMonoRefute.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.ReimerClose2.Part4
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

open ConfigSpace


theorem slice_disjointOccurrence_true_strong {n : ℕ}
    {A B : Set (ConfigSpace (Fin (n + 1)))} :
    slice (disjointOccurrence A B) true ⊆
      disjointOccurrence (slice A true) (slice B true) := by
  intro ω' hω'
  simp only [slice, Set.mem_setOf_eq, mem_disjointOccurrence] at hω'
  obtain ⟨K, L, hKL, hA, hB⟩ := hω'
  exact ⟨sliceSet K, sliceSet L, sliceSet_disjoint hKL,
    occursOn_slice_true hA, occursOn_slice_true hB⟩


theorem wprob_slice_false_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) false)
      ≤ wprob ψ (disjointOccurrence (slice A false) (slice B false)) :=
  wprob_mono hψ0 slice_disjointOccurrence_false


theorem wprob_slice_true_le {n : ℕ} (ψ : Fin n → Bool → ℝ) (hψ0 : ∀ i b, 0 ≤ ψ i b)
    (A B : Set (ConfigSpace (Fin (n + 1)))) :
    wprob ψ (slice (disjointOccurrence A B) true)
      ≤ wprob ψ (disjointOccurrence (slice A true) (slice B true)) :=
  wprob_mono hψ0 slice_disjointOccurrence_true_strong


end StatMech
