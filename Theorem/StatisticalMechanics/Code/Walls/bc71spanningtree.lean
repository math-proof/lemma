/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc71spanningtree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc70globalforest.Part4
import Theorem.StatisticalMechanics.Code.Percolation.CanonForestCount
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc71_deg3_of_three_neighbours {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {u a₁ a₂ a₃ : V}
    (h₁ : G.Adj u a₁) (h₂ : G.Adj u a₂) (h₃ : G.Adj u a₃)
    (h12 : a₁ ≠ a₂) (h13 : a₁ ≠ a₃) (h23 : a₂ ≠ a₃) :
    3 ≤ G.degree u := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : ({a₁, a₂, a₃} : Finset V) ⊆ G.neighborFinset u := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rw [SimpleGraph.mem_neighborFinset]
    rcases hw with rfl | rfl | rfl
    · exact h₁
    · exact h₂
    · exact h₃
  calc (3 : ℕ) = ({a₁, a₂, a₃} : Finset V).card := by
        rw [Finset.card_insert_of_notMem (by simp [h12, h13]),
          Finset.card_insert_of_notMem (by simp [h23]), Finset.card_singleton]
    _ ≤ (G.neighborFinset u).card := Finset.card_le_card hsub


theorem bc71_cutArms_distinct (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y a₁ a₂ a₃ : Site d}
    (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂)
    (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃)
    (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) :
    a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃ := by
  refine ⟨?_, ?_, ?_⟩
  · intro h; exact hcut₁₂ (h ▸ SimpleGraph.Reachable.refl _)
  · intro h; exact hcut₁₃ (h ▸ SimpleGraph.Reachable.refl _)
  · intro h; exact hcut₂₃ (h ▸ SimpleGraph.Reachable.refl _)


theorem bc71_Gn_trifurcation_arms_distinct (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) {y : Site d}
    (h : bc67_IsGnTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, _, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hincs, bc71_cutArms_distinct ω L hcut₁₂ hcut₁₃ hcut₂₃⟩


theorem bc71_deg3_of_cutArms_subtype (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    {S : Set (Site d)} [Fintype (↑S : Type)] (G : SimpleGraph (↑S : Type)) [DecidableRel G.Adj]
    {u v₁ v₂ v₃ : (↑S : Type)}
    (hadj₁ : G.Adj u v₁) (hadj₂ : G.Adj u v₂) (hadj₃ : G.Adj u v₃)
    (hcut₁₂ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₂ : Site d))
    (hcut₁₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₁ : Site d) (v₃ : Site d))
    (hcut₂₃ : ¬ (bc67_contractedLattice ω L y).Reachable (v₂ : Site d) (v₃ : Site d)) :
    3 ≤ G.degree u := by
  obtain ⟨h12, h13, h23⟩ := bc71_cutArms_distinct ω L hcut₁₂ hcut₁₃ hcut₂₃
  
  have hv12 : v₁ ≠ v₂ := fun h => h12 (congrArg Subtype.val h)
  have hv13 : v₁ ≠ v₃ := fun h => h13 (congrArg Subtype.val h)
  have hv23 : v₂ ≠ v₃ := fun h => h23 (congrArg Subtype.val h)
  exact bc71_deg3_of_three_neighbours G hadj₁ hadj₂ hadj₃ hv12 hv13 hv23


end StatMech.Walls
