/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LatticeMengerAttach.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationExistence2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BoxMengerAttachment.Part3
import Def.StatisticalMechanics.Code.Percolation.LatticeMengerAttach
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma lma_mem_corridorEdges {j : Fin d} {L : ℕ} {t : ℕ} (ht : t < L) :
    s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ lma_corridorEdges j L := by
  rw [lma_corridorEdges, Finset.mem_image]; exact ⟨t, Finset.mem_range.mpr ht, rfl⟩


@[simp] lemma lma_corridorEdges_zero (j : Fin d) : lma_corridorEdges j 0 = ∅ := by
  rw [lma_corridorEdges]; simp


lemma lma_origin_notMem_corridorEdges (j : Fin d) (L : ℕ) :
    ∀ e ∈ lma_corridorEdges j L, (0 : Site d) ∉ e := by
  rw [lma_corridorEdges]
  intro e he
  rw [Finset.mem_image] at he
  obtain ⟨t, _, rfl⟩ := he
  simp only [Sym2.mem_iff]
  push Not
  refine ⟨?_, ?_⟩
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega
  · intro h; rw [eq_comm, hrHD_rayPt_eq_zero_iff] at h; omega


lemma lma_corridor_step_open (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (t : ℕ)
    (ht : t < L) :
    IsOpenEdge d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j ((t : ℤ) + 1)) (hrHD_rayPt j ((t : ℤ) + 2)) := by
  refine ⟨?_, ?_⟩
  · have h := hrHD_adj_rayPt j ((t : ℤ) + 1)
    have he : ((t : ℤ) + 1 + 1) = ((t : ℤ) + 2) := by ring
    rwa [he] at h
  · have hmem : s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) ∈ lma_corridorEdges j L :=
      lma_mem_corridorEdges ht
    have hno0 : (0 : Site d) ∉ s(hrHD_rayPt j ((t : ℤ) + 1), hrHD_rayPt j ((t : ℤ) + 2)) :=
      lma_origin_notMem_corridorEdges j L _ hmem
    rw [removeSite_apply_of_notMem hno0, forceOpenFinset_of_mem hmem]


lemma lma_corridor_connected (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d) (L : ℕ) (m : ℕ)
    (hm : m ≤ L) :
    Connected d (removeSite 0 (forceOpenFinset (lma_corridorEdges j L) ω))
      (hrHD_rayPt j 1) (hrHD_rayPt j ((m : ℤ) + 1)) := by
  set ω' := removeSite (0 : Site d) (forceOpenFinset (lma_corridorEdges j L) ω) with hω'
  induction m with
  | zero => simpa using connected_rfl
  | succ p ih =>
    have hpL : p < L := by omega
    have hstep : IsOpenEdge d ω' (hrHD_rayPt j ((p : ℤ) + 1)) (hrHD_rayPt j ((p : ℤ) + 2)) :=
      lma_corridor_step_open ω j L p hpL
    have hrec := ih (by omega)
    have hgoal := hrec.trans hstep.connected
    have he : ((p : ℤ) + 2) = (((p : ℕ) + 1 : ℕ) : ℤ) + 1 := by push_cast; ring
    rwa [he] at hgoal


end Percolation
end StatMech
