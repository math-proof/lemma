/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TwoFoldHallClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tfh_twoFold_hall_root {V : Type*} [DecidableEq V] (T : Finset V)
    (rootEnds : Finset V) (armEnds : V → Fin 2 → Finset V)
    (hrne : rootEnds.Nonempty)
    (hne : ∀ x ∈ T, ∀ i, (armEnds x i).Nonempty)
    (hrdisj : ∀ x ∈ T, ∀ i, Disjoint rootEnds (armEnds x i))
    (hdisj : ∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, (x, i) ≠ (y, j) →
      Disjoint (armEnds x i) (armEnds y j)) :
    ∃ (r₀ : V) (ℓ : V → Fin 2 → V),
      r₀ ∈ rootEnds ∧
      (∀ x ∈ T, ∀ i, ℓ x i ∈ armEnds x i) ∧
      (∀ x ∈ T, ∀ i, ℓ x i ≠ r₀) ∧
      (∀ x ∈ T, ∀ i, ∀ y ∈ T, ∀ j, ℓ x i = ℓ y j → x = y ∧ i = j) := by
  classical
  
  set ι := Option ({x // x ∈ T} × Fin 2) with hι
  set t : ι → Finset V := fun p => p.elim rootEnds (fun q => armEnds q.1.1 q.2) with ht
  
  have hHall : ∀ s : Finset ι, s.card ≤ (s.biUnion t).card := by
    intro s
    rw [Finset.card_biUnion]
    · calc s.card = ∑ _p ∈ s, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
        _ ≤ ∑ p ∈ s, (t p).card := by
            apply Finset.sum_le_sum
            intro p _
            cases p with
            | none => exact Finset.Nonempty.card_pos hrne
            | some q => exact Finset.Nonempty.card_pos (hne q.1.1 q.1.2 q.2)
    · 
      intro p _ q _ hpq
      cases p with
      | none =>
        cases q with
        | none => exact absurd rfl hpq
        | some q' => exact hrdisj q'.1.1 q'.1.2 q'.2
      | some p' =>
        cases q with
        | none => exact (hrdisj p'.1.1 p'.1.2 p'.2).symm
        | some q' =>
          apply hdisj p'.1.1 p'.1.2 p'.2 q'.1.1 q'.1.2 q'.2
          intro hcontra
          apply hpq
          rw [Prod.mk.injEq] at hcontra
          exact congrArg some (Prod.ext (Subtype.ext hcontra.1) hcontra.2)
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHall
  refine ⟨f none, fun x i => if hx : x ∈ T then f (some (⟨x, hx⟩, i)) else x, ?_, ?_, ?_, ?_⟩
  · exact hmem none
  · intro x hx i; simp only [dif_pos hx]; exact hmem (some (⟨x, hx⟩, i))
  · intro x hx i hcontra
    simp only [dif_pos hx] at hcontra
    have : (some (⟨x, hx⟩, i) : ι) = none := hinj hcontra
    exact absurd this (by simp)
  · intro x hx i y hy j hxy
    simp only [dif_pos hx, dif_pos hy] at hxy
    have := hinj hxy
    rw [Option.some.injEq, Prod.mk.injEq] at this
    exact ⟨congrArg Subtype.val this.1, this.2⟩


end Percolation
end StatMech
