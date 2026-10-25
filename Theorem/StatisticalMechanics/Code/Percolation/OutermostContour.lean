/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutermostContour.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem outC_natAbs_succ (j : ℕ) : ((j : ℤ) + 1).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]; left; push_cast; ring


theorem outC_natAbs_neg_succ (j : ℕ) : (-((j : ℤ) + 1)).natAbs = j + 1 := by
  rw [Int.natAbs_eq_iff]; right; push_cast; ring


theorem outC_exitHead_mem_exterior_iff (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (exitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ exitIndex (ω := ω) hfin := by
  rw [exitDart_head]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · have hval : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2) ⟨0, by omega⟩
          = (exitIndex (ω := ω) hfin : ℤ) + 1 := by simp [axisSite]
      rw [hval, outC_natAbs_succ] at hi; omega
    · simp [axisSite] at hi
  · intro h
    refine ⟨0, ?_⟩
    have hval : (axisSite (exitIndex (ω := ω) hfin + 1) : Site 2) 0
        = (exitIndex (ω := ω) hfin : ℤ) + 1 := by simp [axisSite]
    rw [hval, outC_natAbs_succ]; omega


theorem outC_leftExitHead_mem_exterior_iff (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (leftExitDart (ω := ω) hfin).head ∈ exterior 2 R ↔ R ≤ leftExitIndex (ω := ω) hfin := by
  rw [leftExitDart_head]
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) ⟨0, by omega⟩
          = -((leftExitIndex (ω := ω) hfin : ℤ) + 1) := by
        rw [leftAxisSite_succ_eq]; simp; ring
      rw [hval, outC_natAbs_neg_succ] at hi; omega
    · have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) ⟨1, by omega⟩
          = 0 := by rw [leftAxisSite_succ_eq]; simp
      rw [hval] at hi; simp at hi
  · intro h
    refine ⟨0, ?_⟩
    have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin + 1) : Site 2) 0
        = -((leftExitIndex (ω := ω) hfin : ℤ) + 1) := by
      rw [leftAxisSite_succ_eq]; simp; ring
    rw [hval, outC_natAbs_neg_succ]; omega


theorem outC_clusterBox_ge_exitIndex (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) : exitIndex (ω := ω) hfin ≤ R := by
  have hmem := axisSite_exit_mem (ω := ω) hfin
  have hbox := hR hmem
  have h0 := hbox 0
  simpa [axisSite] using h0


theorem outC_clusterBox_ge_leftExitIndex (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) : leftExitIndex (ω := ω) hfin ≤ R := by
  have hmem := leftAxisSite_exit_mem (ω := ω) hfin
  have hbox := hR hmem
  have h0 := hbox 0
  have hval : (leftAxisSite (leftExitIndex (ω := ω) hfin) : Site 2) 0
      = -(leftExitIndex (ω := ω) hfin : ℤ) := rfl
  rw [hval] at h0
  rwa [Int.natAbs_neg, Int.natAbs_natCast] at h0


theorem outC_pcFarExitHeadsFar_forces_eq (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : pcFar_ExitHeadsFar ω hfin) :
    ∃ R : ℕ, R = exitIndex (ω := ω) hfin ∧ R = leftExitIndex (ω := ω) hfin ∧
      cluster 2 ω (origin 2) ⊆ box 2 (exitIndex (ω := ω) hfin) := by
  obtain ⟨R, hR, hr, hl⟩ := h
  have h1 : R ≤ exitIndex (ω := ω) hfin := (outC_exitHead_mem_exterior_iff (ω := ω) hfin R).mp hr
  have h2 : exitIndex (ω := ω) hfin ≤ R := outC_clusterBox_ge_exitIndex (ω := ω) hfin R hR
  have h3 : R ≤ leftExitIndex (ω := ω) hfin :=
    (outC_leftExitHead_mem_exterior_iff (ω := ω) hfin R).mp hl
  have h4 : leftExitIndex (ω := ω) hfin ≤ R := outC_clusterBox_ge_leftExitIndex (ω := ω) hfin R hR
  have hRe : R = exitIndex (ω := ω) hfin := le_antisymm h1 h2
  have hRl : R = leftExitIndex (ω := ω) hfin := le_antisymm h3 h4
  refine ⟨R, hRe, hRl, ?_⟩
  rw [← hRe]; exact hR


theorem outC_pcFarExitHeadsFar_imp_exitIndex_eq (hfin : (cluster 2 ω (origin 2)).Finite)
    (h : pcFar_ExitHeadsFar ω hfin) :
    exitIndex (ω := ω) hfin = leftExitIndex (ω := ω) hfin := by
  obtain ⟨R, hRe, hRl, _⟩ := outC_pcFarExitHeadsFar_forces_eq (ω := ω) hfin h
  rw [← hRe, ← hRl]


theorem outC_not_pcFarExitHeadsFar_of_exitIndex_ne (hfin : (cluster 2 ω (origin 2)).Finite)
    (hne : exitIndex (ω := ω) hfin ≠ leftExitIndex (ω := ω) hfin) :
    ¬ pcFar_ExitHeadsFar ω hfin :=
  fun h => hne (outC_pcFarExitHeadsFar_imp_exitIndex_eq (ω := ω) hfin h)


theorem outC_farBox (hfin : (cluster 2 ω (origin 2)).Finite) :
    ∃ R : ℕ, cluster 2 ω (origin 2) ⊆ box 2 R :=
  exists_clusterBox (ω := ω) hfin


theorem outC_axisFarRight_mem_exterior (R : ℕ) : (![(R : ℤ) + 1, 0] : Site 2) ∈ exterior 2 R :=
  axisFarRight_mem_exterior R


theorem outC_axisFarLeft_mem_exterior (R : ℕ) : (![-((R : ℤ) + 1), 0] : Site 2) ∈ exterior 2 R :=
  axisFarLeft_mem_exterior R


theorem outC_axisFar_reachable (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨![(R : ℤ) + 1, 0], exterior_subset_compl _ R hR (outC_axisFarRight_mem_exterior R)⟩
      ⟨![-((R : ℤ) + 1), 0], exterior_subset_compl _ R hR (outC_axisFarLeft_mem_exterior R)⟩ :=
  axisFar_reachable_in_clusterComplement R hR


theorem outC_axisFarRight_mem_compl (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (![(R : ℤ) + 1, 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ :=
  exterior_subset_compl _ R hR (outC_axisFarRight_mem_exterior R)

theorem outC_axisFarLeft_mem_compl (R : ℕ) (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    (![-((R : ℤ) + 1), 0] : Site 2) ∈ (cluster 2 ω (origin 2))ᶜ :=
  exterior_subset_compl _ R hR (outC_axisFarLeft_mem_exterior R)


end Percolation
end StatMech
