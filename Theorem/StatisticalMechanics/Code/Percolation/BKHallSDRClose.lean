/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BKHallSDRClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bhs_exists_injOn_of_hall {V : Type*} [DecidableEq V] (T : Finset V)
    (armEnds : V → Finset V)
    (hHall : ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card) :
    ∃ φ : V → V, (∀ x ∈ T, φ x ∈ armEnds x) ∧ Set.InjOn φ T := by
  classical
  
  set t : {x // x ∈ T} → Finset V := fun i => armEnds i.1 with ht
  have hHallSub : ∀ s : Finset {x // x ∈ T}, s.card ≤ (s.biUnion t).card := by
    intro s
    set S : Finset V := s.image (fun i => i.1) with hS
    have hSsub : S ⊆ T := by
      intro x hx
      rw [hS, Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact i.2
    have hcardS : S.card = s.card := by
      rw [hS, Finset.card_image_of_injective]
      exact fun a b hab => Subtype.ext hab
    have hbiUnion : s.biUnion t = S.biUnion armEnds := by
      ext z
      simp only [Finset.mem_biUnion, ht, hS, Finset.mem_image]
      constructor
      · rintro ⟨i, hi, hz⟩; exact ⟨i.1, ⟨i, hi, rfl⟩, hz⟩
      · rintro ⟨x, ⟨i, hi, rfl⟩, hz⟩; exact ⟨i, hi, hz⟩
    rw [← hcardS, hbiUnion]
    exact hHall S hSsub
  obtain ⟨f, hinj, hmem⟩ :=
    (Finset.all_card_le_biUnion_card_iff_exists_injective t).mp hHallSub
  refine ⟨fun x => if hx : x ∈ T then f ⟨x, hx⟩ else x, ?_, ?_⟩
  · intro x hx
    simp only [dif_pos hx]
    exact hmem ⟨x, hx⟩
  · intro x hx y hy hxy
    simp only [Finset.mem_coe] at hx hy
    simp only [dif_pos hx, dif_pos hy] at hxy
    exact congrArg Subtype.val (hinj hxy)


theorem bhs_hall_of_pairwiseDisjoint {V : Type*} [DecidableEq V] (T : Finset V)
    (armEnds : V → Finset V)
    (hne : ∀ x ∈ T, (armEnds x).Nonempty)
    (hdisj : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → Disjoint (armEnds x) (armEnds y)) :
    ∀ S : Finset V, S ⊆ T → S.card ≤ (S.biUnion armEnds).card := by
  classical
  intro S hS
  rw [Finset.card_biUnion (fun x hx y hy hxy => hdisj x (hS hx) y (hS hy) hxy)]
  calc S.card = ∑ _x ∈ S, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    _ ≤ ∑ x ∈ S, (armEnds x).card :=
        Finset.sum_le_sum (fun x hx => Finset.Nonempty.card_pos (hne x (hS hx)))


end Percolation
end StatMech
