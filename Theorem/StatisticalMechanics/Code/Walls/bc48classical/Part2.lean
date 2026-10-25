/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc48classical.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc47trifarms.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc46funnelproof.Part6
import Def.StatisticalMechanics.Code.Walls.bc48classical.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc48_Tcount_classical_eq (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_Tcount_classical d ω n = (bc48_classicalTrifFinset ω n).card := rfl


theorem bc48_classicalTrifFinset_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_classicalTrifFinset ω n ⊆ tfc_trifFinset ω n := by
  intro x hx
  rw [bc48_mem_classicalTrifFinset] at hx
  rw [tfc_mem_trifFinset]
  exact ⟨hx.1, bc47_isTrifurcation_of_classical ω x hx.2⟩


theorem bc48_Tcount_classical_le_Tcount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc48_Tcount_classical d ω n ≤ Tcount d ω n := by
  rw [bc48_Tcount_classical_eq, ← tfc_trifFinset_card]
  exact Finset.card_le_card (bc48_classicalTrifFinset_subset ω n)


theorem bc48_classical_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x : Site d) (hxbox : x ∈ box d n) (hcl : bc47_IsClassicalTrifurcation ω x) :
    ∃ a₁ a₂ a₃ : Site d,
      (a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃) ∧
      ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
      (¬ Connected d (removeSite x ω) a₁ a₂ ∧
       ¬ Connected d (removeSite x ω) a₁ a₃ ∧
       ¬ Connected d (removeSite x ω) a₂ a₃) ∧
      (∃ z₁ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₁ z₁) ∧
      (∃ z₂ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₂ z₂) ∧
      (∃ z₃ ∈ vertexBoundary d (n + 1), Connected d (removeSite x ω) a₃ z₃) := by
  obtain ⟨a₁, a₂, a₃, hne, ⟨he1, he2, he3⟩, ⟨hi1, hi2, hi3⟩, hsep⟩ := hcl
  
  have hadj1 : (openSubgraph d ω).Adj x a₁ := he1
  have hadj2 : (openSubgraph d ω).Adj x a₂ := he2
  have hadj3 : (openSubgraph d ω).Adj x a₃ := he3
  
  have hb1 : a₁ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he1.1
  have hb2 : a₂ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he2.1
  have hb3 : a₃ ∈ box d (n + 1) := arc_neighbour_in_box_succ hxbox he3.1
  
  have hax1 : a₁ ≠ x := (he1.1.ne).symm
  have hax2 : a₂ ≠ x := (he2.1.ne).symm
  have hax3 : a₃ ≠ x := (he3.1.ne).symm
  
  obtain ⟨z₁, hz1b, hz1c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₁ hax1 hb1 hi1
  obtain ⟨z₂, hz2b, hz2c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₂ hax2 hb2 hi2
  obtain ⟨z₃, hz3b, hz3c⟩ :=
    arc_connected_removeSite_reaches_boundary ω (n + 1) (by omega) x a₃ hax3 hb3 hi3
  exact ⟨a₁, a₂, a₃, hne, ⟨hadj1, hadj2, hadj3⟩, hsep,
    ⟨z₁, hz1b, hz1c⟩, ⟨z₂, hz2b, hz2c⟩, ⟨z₃, hz3b, hz3c⟩⟩


end StatMech.Walls
