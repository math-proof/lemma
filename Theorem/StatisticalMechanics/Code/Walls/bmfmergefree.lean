/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bmfmergefree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bdecdecouple
import Def.StatisticalMechanics.Code.Walls.bmfmergefree
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech.Walls

set_option linter.style.longLine false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

set_option maxRecDepth 4000


theorem bmf_o_ne_a₁ : (0 : Site 2) ≠ bmf_a₁ := by
  intro h; have := congrFun h 0; simp [bmf_a₁] at this

theorem bmf_o_ne_a₂ : (0 : Site 2) ≠ bmf_a₂ := by
  intro h; have := congrFun h 1; simp [bmf_a₂] at this

theorem bmf_o_ne_a₃ : (0 : Site 2) ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₃] at this

theorem bmf_o_ne_b₁ : (0 : Site 2) ≠ bmf_b₁ := by
  intro h; have := congrFun h 0; simp [bmf_b₁] at this

theorem bmf_o_ne_b₂ : (0 : Site 2) ≠ bmf_b₂ := by
  intro h; have := congrFun h 1; simp [bmf_b₂] at this

theorem bmf_o_ne_b₃ : (0 : Site 2) ≠ bmf_b₃ := by
  intro h; have := congrFun h 0; simp [bmf_b₃] at this


theorem bmf_a₁_ne_a₂ : bmf_a₁ ≠ bmf_a₂ := by
  intro h; have := congrFun h 0; simp [bmf_a₁, bmf_a₂] at this

theorem bmf_a₁_ne_a₃ : bmf_a₁ ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₁, bmf_a₃] at this

theorem bmf_a₂_ne_a₃ : bmf_a₂ ≠ bmf_a₃ := by
  intro h; have := congrFun h 0; simp [bmf_a₂, bmf_a₃] at this


theorem bmf_adj_o_a₁ : (hypercubicLattice 2).Adj 0 bmf_a₁ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₁, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

theorem bmf_adj_o_a₂ : (hypercubicLattice 2).Adj 0 bmf_a₂ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₂, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

theorem bmf_adj_o_a₃ : (hypercubicLattice 2).Adj 0 bmf_a₃ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₃, Pi.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide


theorem bmf_adj_a₁_b₁ : (hypercubicLattice 2).Adj bmf_a₁ bmf_b₁ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₁, bmf_b₁,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

theorem bmf_adj_a₂_b₂ : (hypercubicLattice 2).Adj bmf_a₂ bmf_b₂ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₂, bmf_b₂,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide

theorem bmf_adj_a₃_b₃ : (hypercubicLattice 2).Adj bmf_a₃ bmf_b₃ := by
  simp only [hypercubicLattice_adj, Fin.sum_univ_two, bmf_a₃, bmf_b₃,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  decide


theorem bmf_o_notMem_e₁ : (0 : Site 2) ∉ s(bmf_a₁, bmf_b₁) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₁, bmf_o_ne_b₁⟩

theorem bmf_o_notMem_e₂ : (0 : Site 2) ∉ s(bmf_a₂, bmf_b₂) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₂, bmf_o_ne_b₂⟩

theorem bmf_o_notMem_e₃ : (0 : Site 2) ∉ s(bmf_a₃, bmf_b₃) := by
  rw [Sym2.mem_iff]; push_neg; exact ⟨bmf_o_ne_a₃, bmf_o_ne_b₃⟩


theorem bmf_corridor_open (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    ω s(bmf_a₁, bmf_b₁) = true ∧ ω s(bmf_a₂, bmf_b₂) = true ∧
      ω s(bmf_a₃, bmf_b₃) = true := by
  rw [mem_cylinder, Set.mem_singleton_iff] at hω
  have h1 : bmf_I.restrict ω ⟨s(bmf_a₁, bmf_b₁), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₁, bmf_b₁), by simp [bmf_I]⟩ := by rw [hω]
  have h2 : bmf_I.restrict ω ⟨s(bmf_a₂, bmf_b₂), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₂, bmf_b₂), by simp [bmf_I]⟩ := by rw [hω]
  have h3 : bmf_I.restrict ω ⟨s(bmf_a₃, bmf_b₃), by simp [bmf_I]⟩
      = bmf_η₀ ⟨s(bmf_a₃, bmf_b₃), by simp [bmf_I]⟩ := by rw [hω]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Finset.restrict, bmf_η₀] using h1
  · simpa [Finset.restrict, bmf_η₀] using h2
  · simpa [Finset.restrict, bmf_η₀] using h3


theorem bmf_conn_a₁_b₁ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₁ bmf_b₁ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₁_b₁, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₁]
  exact (bmf_corridor_open ω hω).1

theorem bmf_conn_a₂_b₂ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₂ bmf_b₂ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₂_b₂, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₂]
  exact (bmf_corridor_open ω hω).2.1

theorem bmf_conn_a₃_b₃ (ω : ConfigSpace (Sym2 (Site 2)))
    (hω : ω ∈ cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I))) :
    Connected 2 (removeSite 0 ω) bmf_a₃ bmf_b₃ := by
  apply IsOpenEdge.connected
  refine ⟨bmf_adj_a₃_b₃, ?_⟩
  rw [removeSite_apply_of_notMem bmf_o_notMem_e₃]
  exact (bmf_corridor_open ω hω).2.2


theorem bmf_hgeo :
    cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X
      ⊆ NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃ := by
  rintro ω ⟨hcyl, hX⟩
  obtain ⟨⟨hb1inf, hb2inf, hb3inf⟩, hb12, hb13, hb23⟩ := hX
  have c1 := bmf_conn_a₁_b₁ ω hcyl
  have c2 := bmf_conn_a₂_b₂ ω hcyl
  have c3 := bmf_conn_a₃_b₃ ω hcyl
  refine ⟨⟨bmf_a₁_ne_a₂, bmf_a₁_ne_a₃, bmf_a₂_ne_a₃⟩,
    ⟨bmf_adj_o_a₁, bmf_adj_o_a₂, bmf_adj_o_a₃⟩, ?_, ?_⟩
  · 
    refine ⟨?_, ?_, ?_⟩
    · rw [cluster_eq_of_connected c1]; exact hb1inf
    · rw [cluster_eq_of_connected c2]; exact hb2inf
    · rw [cluster_eq_of_connected c3]; exact hb3inf
  · 
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact hb12 (c1.symm.trans (h.trans c2))
    · intro h; exact hb13 (c1.symm.trans (h.trans c3))
    · intro h; exact hb23 (c2.symm.trans (h.trans c3))


theorem bmf_precursorPos_of_residues (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1)
    (hindep : bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)) ∩ bmf_X)
        = bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
            (cylinder bmf_I ({bmf_η₀} : Set (ConfigSpace ↥bmf_I)))
          * bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X)
    (hXpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 bmf_X) :
    0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (NeighborTrifPrecursor 2 bmf_a₁ bmf_a₂ bmf_a₃) :=
  bdec_precursorPos_of_decoupled p hp1 hp0 hplt bmf_a₁ bmf_a₂ bmf_a₃ bmf_I bmf_η₀ bmf_X
    hindep hXpos bmf_hgeo


end StatMech.Walls
