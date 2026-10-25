/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.MengerCorridors.Part3
import Def.StatisticalMechanics.Code.Percolation.TrifurcationExistence.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem tre_insertion_of_boxResidue {n : ℕ} (h : tre_BoxMergeFreeInsertion d n)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ threeMeetBox d n) :
    tre_MergeFreeInsertion ω := h ω hω


theorem tre_threeClustersReachOrigin_of_finiteEnergy {n : ℕ}
    (h : tre_BoxMergeFreeInsertion d n) :
    ∀ ω ∈ threeMeetBox d n, ∃ W : Finset (Sym2 (Site d)),
      mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
  intro ω hω
  exact tre_threeClustersReachOrigin_of_insertion ω (tre_insertion_of_boxResidue h hω)


theorem tre_forceOpenFinset_comp (F W : Finset (Sym2 (Site d)))
    (ω : ConfigSpace (Sym2 (Site d))) :
    forceOpenFinset F (forceOpenFinset W ω) = forceOpenFinset (F ∪ W) ω := by
  funext e
  unfold forceOpenFinset
  by_cases hF : e ∈ F
  · simp [hF, Finset.mem_union]
  · by_cases hW : e ∈ W <;> simp [hF, hW, Finset.mem_union]


theorem tre_precursor_of_modifiedMergeFree (ω : ConfigSpace (Sym2 (Site d)))
    (W : Finset (Sym2 (Site d))) (h : bka_MergeFree (forceOpenFinset W ω)) :
    ∃ (G : Finset (Sym2 (Site d))) (a₁ a₂ a₃ : Site d),
      forceOpenFinset G ω ∈ NeighborTrifPrecursor d a₁ a₂ a₃ := by
  classical
  set ωW := forceOpenFinset W ω with hωW
  obtain ⟨a₁, a₂, a₃, hne, hadj, ⟨hi1, hi2, hi3⟩, hd12, hd13, hd23⟩ := h
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with hh | hh | hh <;> (rw [hh]; exact Sym2.mem_mk_left _ _)
  have hrm : removeSite (0:Site d) (forceOpenFinset F ωW) = removeSite (0:Site d) ωW :=
    removeSite_forceOpen_eq 0 F hFmem ωW
  refine ⟨F ∪ W, a₁, a₂, a₃, ?_⟩
  rw [← tre_forceOpenFinset_comp F W ω, ← hωW]
  refine ⟨hne, hadj, ?_, ?_, ?_, ?_⟩
  · rw [hrm]; exact ⟨hi1, hi2, hi3⟩
  · rw [hrm]; intro hc; exact hd12 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd13 (cluster_eq_of_connected hc)
  · rw [hrm]; intro hc; exact hd23 (cluster_eq_of_connected hc)


theorem tre_disjointRouting_of_finiteEnergy {n : ℕ}
    (h : tre_BoxMergeFreeInsertion d n) : hrHD_DisjointRouting d n := by
  intro ω hω
  obtain ⟨W, hmf⟩ := tre_mergeFree_of_insertion ω (tre_insertion_of_boxResidue h hω)
  exact tre_precursor_of_modifiedMergeFree ω W hmf


end Percolation
end StatMech
