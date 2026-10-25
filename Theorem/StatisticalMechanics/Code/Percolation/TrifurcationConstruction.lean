/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/TrifurcationConstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem removeSite_forceOpen_eq (x : Site d) (F : Finset (Sym2 (Site d)))
    (hF : ∀ e ∈ F, x ∈ e) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x (forceOpenFinset F ω) = removeSite x ω := by
  funext e
  unfold removeSite forceOpenFinset
  by_cases hx : x ∈ e
  · simp [hx]
  · simp only [hx, if_false]
    by_cases hef : e ∈ F
    · exact absurd (hF e hef) hx
    · simp [hef]


theorem removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSite x ω ≤ ω := by
  intro e; unfold removeSite; by_cases hx : x ∈ e <;> simp [hx]


theorem isTrifurcation_of_neighbors
    (ω : ConfigSpace (Sym2 (Site d)))
    (a₁ a₂ a₃ : Site d)
    (hne : a₁ ≠ a₂ ∧ a₁ ≠ a₃ ∧ a₂ ≠ a₃)
    (hadj1 : (hypercubicLattice d).Adj 0 a₁)
    (hadj2 : (hypercubicLattice d).Adj 0 a₂)
    (hadj3 : (hypercubicLattice d).Adj 0 a₃)
    (hinf1 : (cluster d (removeSite 0 ω) a₁).Infinite)
    (hinf2 : (cluster d (removeSite 0 ω) a₂).Infinite)
    (hinf3 : (cluster d (removeSite 0 ω) a₃).Infinite)
    (hsep12 : ¬ Connected d (removeSite 0 ω) a₁ a₂)
    (hsep13 : ¬ Connected d (removeSite 0 ω) a₁ a₃)
    (hsep23 : ¬ Connected d (removeSite 0 ω) a₂ a₃) :
    IsTrifurcation d
      (forceOpenFinset {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} ω) 0 := by
  classical
  set F : Finset (Sym2 (Site d)) :=
    {s((0:Site d), a₁), s((0:Site d), a₂), s((0:Site d), a₃)} with hFdef
  set ω' := forceOpenFinset F ω with hω'
  
  have hFmem : ∀ e ∈ F, (0 : Site d) ∈ e := by
    intro e he
    simp only [hFdef, Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with h | h | h <;> (rw [h]; exact Sym2.mem_mk_left _ _)
  
  have hrm : removeSite (0:Site d) ω' = removeSite (0:Site d) ω :=
    removeSite_forceOpen_eq 0 F hFmem ω
  
  have hconn1 : Connected d ω' 0 a₁ := by
    apply IsOpenEdge.connected; exact ⟨hadj1, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hconn2 : Connected d ω' 0 a₂ := by
    apply IsOpenEdge.connected; exact ⟨hadj2, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  have hconn3 : Connected d ω' 0 a₃ := by
    apply IsOpenEdge.connected; exact ⟨hadj3, forceOpenFinset_of_mem (by simp [hFdef]) ω⟩
  
  have hle : removeSite (0:Site d) ω ≤ ω' := by rw [← hrm]; exact removeSite_le 0 ω'
  have hinf1' : (cluster d ω' a₁).Infinite := hinf1.mono (cluster_mono hle a₁)
  have hinf2' : (cluster d ω' a₂).Infinite := hinf2.mono (cluster_mono hle a₂)
  have hinf3' : (cluster d ω' a₃).Infinite := hinf3.mono (cluster_mono hle a₃)
  
  refine ⟨a₁, a₂, a₃, hne, ⟨hconn1, hconn2, hconn3⟩, ⟨hinf1', hinf2', hinf3'⟩, ?_⟩
  rw [hrm]
  exact ⟨hsep12, hsep13, hsep23⟩


end Percolation
end StatMech
