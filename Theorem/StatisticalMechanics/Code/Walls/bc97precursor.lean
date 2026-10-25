/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc97precursor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc96singlesiterewiring
import Def.StatisticalMechanics.Code.Walls.bc97precursor
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc97_boundaryGenuine_subset_vertexBoundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc97_boundaryGenuineFinset ω n ⊆ (vertexBoundary_finite d n).toFinset := by
  classical
  intro x hx
  rw [bc97_boundaryGenuineFinset, Finset.mem_filter] at hx
  obtain ⟨hxgen, hxnint⟩ := hx
  rw [bc89_genuineTrifFinset, Finset.mem_filter, boxFinsetBK, Set.Finite.mem_toFinset] at hxgen
  rw [Set.Finite.mem_toFinset, mem_vertexBoundary]
  exact ⟨hxgen.1, hxnint⟩


theorem bc97_boundary_genuineCount_le (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    (bc97_boundaryGenuineFinset ω n).card ≤ boxSV_boundaryCard d n := by
  classical
  unfold boxSV_boundaryCard
  exact Finset.card_le_card (bc97_boundaryGenuine_subset_vertexBoundary ω n)


theorem bc97_genuineCount_split (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTcount ω n
      = (bc97_interiorGenuineFinset ω n).card + (bc97_boundaryGenuineFinset ω n).card := by
  classical
  unfold bc89_genuineTcount bc97_interiorGenuineFinset bc97_boundaryGenuineFinset
  exact (Finset.card_filter_add_card_filter_not
    (s := bc89_genuineTrifFinset ω n) (p := fun x => x ∈ box d (n - 1))).symm


theorem bc97_genuineCount_le_interior_plus_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc89_genuineTcount ω n
      ≤ (bc97_interiorGenuineFinset ω n).card + boxSV_boundaryCard d n := by
  rw [bc97_genuineCount_split ω n]
  exact Nat.add_le_add_left (bc97_boundary_genuineCount_le ω n) _


theorem bc97_interior_harmbox_free (ω : ConfigSpace (Sym2 (Site d))) {n : ℕ} (hn : 1 ≤ n)
    {x : Site d} (hxint : x ∈ box d (n - 1))
    {a : Site d} (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d n :=
  bc90_harmbox_free_of_interior ω hn hxint hadj


theorem bc97_forceOrigin_genuineTrif (ω : ConfigSpace (Sym2 (Site d)))
    {a₁ a₂ a₃ x₁ x₂ x₃ : Site d}
    (hadj : (hypercubicLattice d).Adj 0 a₁ ∧ (hypercubicLattice d).Adj 0 a₂ ∧
      (hypercubicLattice d).Adj 0 a₃)
    (hconn : Connected d (removeSite 0 ω) a₁ x₁ ∧ Connected d (removeSite 0 ω) a₂ x₂ ∧
      Connected d (removeSite 0 ω) a₃ x₃)
    (hinf : (cluster d (removeSite 0 ω) x₁).Infinite ∧
      (cluster d (removeSite 0 ω) x₂).Infinite ∧ (cluster d (removeSite 0 ω) x₃).Infinite)
    (hdist : cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₂ ∧
      cluster d (removeSite 0 ω) x₁ ≠ cluster d (removeSite 0 ω) x₃ ∧
      cluster d (removeSite 0 ω) x₂ ≠ cluster d (removeSite 0 ω) x₃) :
    bc89_GenuineTrif d (forceOpenFinset {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} ω) 0 := by
  classical
  set F : Finset (Sym2 (Site d)) := {s((0 : Site d), a₁), s(0, a₂), s(0, a₃)} with hFdef
  set ω' := forceOpenFinset F ω with hω'
  obtain ⟨hadj1, hadj2, hadj3⟩ := hadj
  
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> · rw [h]; exact Sym2.mem_mk_left _ _
  have hrm : removeSite 0 ω' = removeSite 0 ω := removeSite_forceOpen_eq 0 F hFmem ω
  
  have ho1 : ω' s(0, a₁) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  have ho2 : ω' s(0, a₂) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  have ho3 : ω' s(0, a₃) = true := forceOpenFinset_of_mem (by simp [hFdef]) ω
  
  refine bc96_genuineTrif_of_reachOrigin_full ω' (x₁ := x₁) (x₂ := x₂) (x₃ := x₃)
    ⟨hadj1, hadj2, hadj3⟩ ?_ ?_ ?_ ⟨ho1, ho2, ho3⟩
  · rw [hrm]; exact hconn
  · rw [hrm]; exact hinf
  · rw [hrm]; exact hdist


end StatMech.Walls
