/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/BurtonKeaneClose2.lean -/

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
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem bk2_card_le_of_pairwiseDisjoint {α β : Type*} [DecidableEq β]
    (S : Finset α) (T : Finset β) (A : α → Finset β)
    (hne : ∀ x ∈ S, (A x).Nonempty)
    (hsub : ∀ x ∈ S, A x ⊆ T)
    (hdisj : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → Disjoint (A x) (A y)) :
    S.card ≤ T.card := by
  classical
  rcases S.eq_empty_or_nonempty with hS | hS
  · simp [hS]
  · obtain ⟨x₀, hx₀⟩ := hS
    obtain ⟨b₀, _⟩ := hne x₀ hx₀
    
    let φ : α → β := fun x => if h : (A x).Nonempty then h.choose else b₀
    refine Finset.card_le_card_of_injOn φ ?_ ?_
    · intro x hx
      simp only [Finset.mem_coe] at hx ⊢
      have h := hne x hx
      simp only [φ, dif_pos h]
      exact hsub x hx h.choose_spec
    · intro x hx y hy hxy
      simp only [Finset.mem_coe] at hx hy
      by_cases hne' : x = y
      · exact hne'
      · exfalso
        have hAx := hne x hx
        have hAy := hne y hy
        simp only [φ, dif_pos hAx, dif_pos hAy] at hxy
        have hmem : hAx.choose ∈ A x ∩ A y :=
          Finset.mem_inter.mpr ⟨hAx.choose_spec, hxy ▸ hAy.choose_spec⟩
        rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj x hx y hy hne')] at hmem
        exact absurd hmem (Finset.notMem_empty _)


end Percolation
end StatMech
