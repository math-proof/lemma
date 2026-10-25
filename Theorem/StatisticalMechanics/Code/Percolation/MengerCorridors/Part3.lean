/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/MengerCorridors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneAttachment.Part4
import Def.StatisticalMechanics.Code.Percolation.MengerCorridors.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem mco_rayPt_one_mem_corridorVerts (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    hrHD_rayPt j 1 ∈ mco_corridorVerts j L :=
  ⟨1, le_rfl, hL, by norm_num⟩


theorem mco_origin_notMem_corridorVerts (j : Fin d) (L : ℕ) :
    (0 : Site d) ∉ mco_corridorVerts j L := by
  rintro ⟨m, hm1, _, heq⟩
  rw [eq_comm, hrHD_rayPt_eq_zero_iff] at heq
  omega


theorem mco_corridorVerts_disjoint {j₁ j₂ : Fin d} (h : j₁ ≠ j₂) (L : ℕ) :
    Disjoint (mco_corridorVerts j₁ L) (mco_corridorVerts j₂ L) := by
  rw [Set.disjoint_left]
  rintro y ⟨m, hm1, _, rfl⟩ ⟨n, _, _, hn⟩
  have hm0 : (m : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
    omega
  exact hrHD_rayPt_disjoint_of_ne h hm0 hn


theorem mco_corridorVert_connected (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ)
    (m : ℕ) (hm1 : 1 ≤ m) (hmL : m ≤ L) :
    Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j (m : ℤ)) := by
  set ω' := removeSite (0 : Site d) (forceOpenFinset (hrHD_corridorEdges j L) ω) with hω'
  induction m with
  | zero => omega
  | succ p ih =>
    rcases Nat.lt_or_ge 1 (p + 1) with hp | hp
    · have hp1 : 1 ≤ p := by omega
      have hppL : p < L := by omega
      have hstep : IsOpenEdge d ω' (hrHD_rayPt j (p : ℤ)) (hrHD_rayPt j ((p : ℤ) + 1)) :=
        hrHD_corridor_step_open ω j L p hp1 hppL
      have hrec := ih hp1 (by omega)
      have hgoal := hrec.trans hstep.connected
      have he : ((p : ℤ) + 1) = ((p + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [he] at hgoal
    · have hp1 : p + 1 = 1 := by omega
      rw [hp1]; simpa using connected_rfl


theorem mco_corridorVerts_subset_cluster (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (L : ℕ) :
    mco_corridorVerts j L ⊆
      cluster d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j L) ω)) (hrHD_rayPt j 1) := by
  rintro y ⟨m, hm1, hmL, rfl⟩
  rw [mem_cluster]
  exact mco_corridorVert_connected ω j L m hm1 hmL


theorem mco_three_disjoint_corridors (ω : ConfigSpace (Sym2 (Site d)))
    {j₁ j₂ j₃ : Fin d} (h12 : j₁ ≠ j₂) (h13 : j₁ ≠ j₃) (h23 : j₂ ≠ j₃)
    (L : ℕ) (hL : 1 ≤ L) :
    ∃ C₁ C₂ C₃ : Set (Site d),
      (hrHD_rayPt j₁ 1 ∈ C₁ ∧ hrHD_rayPt j₂ 1 ∈ C₂ ∧ hrHD_rayPt j₃ 1 ∈ C₃) ∧
      ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧
        (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
        (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
      ((0 : Site d) ∉ C₁ ∧ (0 : Site d) ∉ C₂ ∧ (0 : Site d) ∉ C₃) ∧
      (Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃) ∧
      ((∀ y ∈ C₁, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω))
          (hrHD_rayPt j₁ 1) y) ∧
        (∀ y ∈ C₂, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω))
          (hrHD_rayPt j₂ 1) y) ∧
        (∀ y ∈ C₃, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω))
          (hrHD_rayPt j₃ 1) y)) := by
  refine ⟨mco_corridorVerts j₁ L, mco_corridorVerts j₂ L, mco_corridorVerts j₃ L,
    ⟨mco_rayPt_one_mem_corridorVerts j₁ L hL, mco_rayPt_one_mem_corridorVerts j₂ L hL,
      mco_rayPt_one_mem_corridorVerts j₃ L hL⟩,
    ⟨hrHD_adj_origin_rayPt_one j₁, hrHD_adj_origin_rayPt_one j₂, hrHD_adj_origin_rayPt_one j₃⟩,
    ⟨mco_origin_notMem_corridorVerts j₁ L, mco_origin_notMem_corridorVerts j₂ L,
      mco_origin_notMem_corridorVerts j₃ L⟩,
    ⟨mco_corridorVerts_disjoint h12 L, mco_corridorVerts_disjoint h13 L,
      mco_corridorVerts_disjoint h23 L⟩, ?_, ?_, ?_⟩
  · rintro y ⟨m, hm1, hmL, rfl⟩; exact mco_corridorVert_connected ω j₁ L m hm1 hmL
  · rintro y ⟨m, hm1, hmL, rfl⟩; exact mco_corridorVert_connected ω j₂ L m hm1 hmL
  · rintro y ⟨m, hm1, hmL, rfl⟩; exact mco_corridorVert_connected ω j₃ L m hm1 hmL


theorem mco_corridors_nonvacuous (j : Fin d) (L : ℕ) (hL : 1 ≤ L) :
    (mco_corridorVerts j L).Nonempty :=
  ⟨hrHD_rayPt j 1, mco_rayPt_one_mem_corridorVerts j L hL⟩


theorem mco_exists_three_disjoint_corridors (ω : ConfigSpace (Sym2 (Site d))) (hd : 3 ≤ d)
    (L : ℕ) (hL : 1 ≤ L) :
    ∃ (j₁ j₂ j₃ : Fin d) (C₁ C₂ C₃ : Set (Site d)),
      (j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃) ∧
      (hrHD_rayPt j₁ 1 ∈ C₁ ∧ hrHD_rayPt j₂ 1 ∈ C₂ ∧ hrHD_rayPt j₃ 1 ∈ C₃) ∧
      ((hypercubicLattice d).Adj 0 (hrHD_rayPt j₁ 1) ∧
        (hypercubicLattice d).Adj 0 (hrHD_rayPt j₂ 1) ∧
        (hypercubicLattice d).Adj 0 (hrHD_rayPt j₃ 1)) ∧
      ((0 : Site d) ∉ C₁ ∧ (0 : Site d) ∉ C₂ ∧ (0 : Site d) ∉ C₃) ∧
      (Disjoint C₁ C₂ ∧ Disjoint C₁ C₃ ∧ Disjoint C₂ C₃) ∧
      ((∀ y ∈ C₁, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₁ L) ω))
          (hrHD_rayPt j₁ 1) y) ∧
        (∀ y ∈ C₂, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₂ L) ω))
          (hrHD_rayPt j₂ 1) y) ∧
        (∀ y ∈ C₃, Connected d (removeSite 0 (forceOpenFinset (hrHD_corridorEdges j₃ L) ω))
          (hrHD_rayPt j₃ 1) y)) := by
  obtain ⟨j₁, j₂, j₃, h12, h13, h23⟩ := hrHD_exists_three_independent_axes hd
  obtain ⟨C₁, C₂, C₃, hmem, hadj, h0, hdisj, hconn⟩ :=
    mco_three_disjoint_corridors ω h12 h13 h23 L hL
  exact ⟨j₁, j₂, j₃, C₁, C₂, C₃, ⟨h12, h13, h23⟩, hmem, hadj, h0, hdisj, hconn⟩

end Percolation
end StatMech
