/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/FarDartContour.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceOrbit.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ExitDartsOrbit
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OutermostContour.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcFarContour
import Def.StatisticalMechanics.Code.Percolation.FarDartContour.Part3
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem fdc_leftExitIdx_le (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    fdc_leftExitIdx (ω := ω) hfin R ≤ R := by
  classical
  rw [fdc_leftExitIdx]; exact Nat.findGreatest_le R


theorem fdc_leftExitIdx_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_leftExitIdx]
  exact Nat.findGreatest_spec (P := fun n => leftAxisSite n ∈ cluster 2 ω (origin 2))
    (Nat.zero_le R) (leftAxisSite_zero_mem_cluster (ω := ω))


theorem fdc_leftExitIdx_is_greatest (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    {k : ℕ} (h1 : fdc_leftExitIdx (ω := ω) hfin R < k) (h2 : k ≤ R) :
    leftAxisSite k ∉ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_leftExitIdx] at h1
  exact Nat.findGreatest_is_greatest h1 h2


theorem fdc_leftRun_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) {k : ℕ}
    (h1 : fdc_leftExitIdx (ω := ω) hfin R + 1 ≤ k) (h2 : k ≤ R + 1) :
    (leftAxisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · exact fdc_leftExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · have hkR : k = R + 1 := heq
    have hext : (leftAxisSite k : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < (-(k : ℤ)).natAbs
      rw [Int.natAbs_neg, show ((k:ℤ)).natAbs = k by exact Int.natAbs_natCast k]
      omega
    exact exterior_subset_compl _ R hR hext


theorem fdc_leftExitIdx_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) :=
  fdc_leftRun_not_mem (ω := ω) hfin R hR (le_refl _)
    (Nat.succ_le_succ (fdc_leftExitIdx_le (ω := ω) hfin R))


theorem fdc_leftExit_adj (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (hypercubicLattice 2).Adj (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R))
      (leftAxisSite (fdc_leftExitIdx (ω := ω) hfin R + 1)) := by
  set n := fdc_leftExitIdx (ω := ω) hfin R
  rw [leftAxisSite_eq n, leftAxisSite_succ_eq n]
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


end Percolation
end StatMech
