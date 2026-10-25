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
import Def.StatisticalMechanics.Code.Percolation.LatticeMengerAttach.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


lemma lma_origin_notMem_corridorVerts (j : Fin d) (L : ℕ) :
    (0 : Site d) ∉ lma_corridorVerts j L := by
  rintro ⟨m, hm1, _, heq⟩
  rw [eq_comm, hrHD_rayPt_eq_zero_iff] at heq; omega


lemma lma_corridorVerts_disjoint {j₁ j₂ : Fin d} (h : j₁ ≠ j₂) (L : ℕ) :
    Disjoint (lma_corridorVerts j₁ L) (lma_corridorVerts j₂ L) := by
  rw [Set.disjoint_left]
  rintro y ⟨m, hm1, _, rfl⟩ ⟨n, _, _, hn⟩
  have hm0 : (m : ℤ) ≠ 0 := by
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm1
    omega
  exact hrHD_rayPt_disjoint_of_ne h hm0 hn


lemma lma_corridorEdges_endpoints_mem (j : Fin d) (L : ℕ) :
    ∀ e ∈ lma_corridorEdges j L, ∀ p, p ∈ e → p ∈ lma_corridorVerts j L := by
  rw [lma_corridorEdges]
  intro e he p hp
  rw [Finset.mem_image] at he
  obtain ⟨t, ht, rfl⟩ := he
  rw [Finset.mem_range] at ht
  rw [Sym2.mem_iff] at hp
  rcases hp with rfl | rfl
  · exact ⟨t + 1, by omega, by omega, by push_cast; ring_nf⟩
  · exact ⟨t + 2, by omega, by omega, by push_cast; ring_nf⟩


lemma lma_removeSite_le_forceOpen (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) :
    removeSite 0 ω ≤ removeSite 0 (forceOpenFinset W ω) := by
  classical
  have h := bma_removeSite_forceOpen_mono_sub ω (Wⱼ := (∅ : Finset (Sym2 (Site d)))) (W := W)
    (Finset.empty_subset W)
  have he : forceOpenFinset (∅ : Finset (Sym2 (Site d))) ω = ω := by
    funext e; simp [forceOpenFinset]
  rwa [he] at h


end Percolation
end StatMech
