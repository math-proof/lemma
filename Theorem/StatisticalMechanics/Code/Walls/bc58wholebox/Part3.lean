/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc58wholebox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc57coarsetrif.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc54coarse
import Theorem.StatisticalMechanics.Code.Walls.bc49finiteenergy
import Theorem.StatisticalMechanics.Code.Percolation.HrouteHighDim.Part3
import Def.StatisticalMechanics.Code.Walls.bc58wholebox.Part3
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


@[simp] theorem bc58_p_fst (a b : ℤ) : (bc58_p a b) 0 = a := by simp [bc58_p]

@[simp] theorem bc58_p_snd (a b : ℤ) : (bc58_p a b) 1 = b := by simp [bc58_p]


theorem bc58_p_mem_box {k : ℕ} {a b : ℤ} (ha : a.natAbs ≤ k) (hb : b.natAbs ≤ k) :
    bc58_p a b ∈ box 2 k := by
  rw [mem_box]; intro i; fin_cases i
  · change ((bc58_p a b) 0).natAbs ≤ k; rw [bc58_p_fst]; exact ha
  · change ((bc58_p a b) 1).natAbs ≤ k; rw [bc58_p_snd]; exact hb


theorem bc58_p_adj_horiz (a b : ℤ) :
    (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p (a + 1) b) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]


theorem bc58_p_adj_vert (a b : ℤ) :
    (hypercubicLattice 2).Adj (bc58_p a b) (bc58_p a (b + 1)) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]


theorem bc58_origin_eq : (0 : Site 2) = bc58_p 0 0 := by
  funext i; fin_cases i <;> simp [bc58_p]


theorem bc58_p_eq_origin_iff {a b : ℤ} : bc58_p a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [bc58_origin_eq]
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp only [bc58_p_fst, bc58_p_snd] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]


theorem bc58_origin_notMem_edge {a b c e : ℤ}
    (h1 : ¬ (a = 0 ∧ b = 0)) (h2 : ¬ (c = 0 ∧ e = 0)) :
    (0 : Site 2) ∉ s(bc58_p a b, bc58_p c e) := by
  rw [Sym2.mem_iff]
  rintro (h | h)
  · exact h1 ((bc58_p_eq_origin_iff).mp h.symm)
  · exact h2 ((bc58_p_eq_origin_iff).mp h.symm)


theorem bc58_reconnect_around_origin {k : ℕ} (hk : 1 ≤ k) (ω : ConfigSpace (Sym2 (Site 2))) :
    Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p (-1) 0) := by
  
  have hk1 : (1 : ℤ).natAbs ≤ k := by simpa using hk
  have hkm1 : ((-1 : ℤ)).natAbs ≤ k := by simpa using hk
  have hk0 : (0 : ℤ).natAbs ≤ k := by simp
  
  have m10 : bc58_p 1 0 ∈ box 2 k := bc58_p_mem_box hk1 hk0
  have m11 : bc58_p 1 1 ∈ box 2 k := bc58_p_mem_box hk1 hk1
  have m01 : bc58_p 0 1 ∈ box 2 k := bc58_p_mem_box hk0 hk1
  have mm11 : bc58_p (-1) 1 ∈ box 2 k := bc58_p_mem_box hkm1 hk1
  have mm10 : bc58_p (-1) 0 ∈ box 2 k := bc58_p_mem_box hkm1 hk0
  
  have s1 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 0) (bc58_p 1 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p 1 0) (bc58_p 1 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact bc58_boxOpen_removeSite_adj_connected m10 m11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω
  
  have s2 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 1 1) (bc58_p 0 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p 0 1) (bc58_p 1 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected m01 m11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  
  have s3 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p 0 1) (bc58_p (-1) 1) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p (-1) 1) (bc58_p 0 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected mm11 m01 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  
  have s4 : Connected 2 (removeSite 0 (bc58_boxOpen 2 k ω)) (bc58_p (-1) 1) (bc58_p (-1) 0) := by
    have hadj : (hypercubicLattice 2).Adj (bc58_p (-1) 0) (bc58_p (-1) 1) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp [bc58_p]
    exact (bc58_boxOpen_removeSite_adj_connected mm10 mm11 hadj
      (bc58_origin_notMem_edge (by decide) (by decide)) ω).symm
  exact (s1.trans s2).trans (s3.trans s4)


end StatMech.Walls
