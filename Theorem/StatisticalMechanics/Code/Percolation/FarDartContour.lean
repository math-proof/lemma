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
import Def.StatisticalMechanics.Code.Percolation.FarDartContour
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem fdc_rightExitIdx_le (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    fdc_rightExitIdx (ω := ω) hfin R ≤ R := by
  classical
  rw [fdc_rightExitIdx]; exact Nat.findGreatest_le R


theorem fdc_rightExitIdx_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    axisSite (fdc_rightExitIdx (ω := ω) hfin R) ∈ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_rightExitIdx]
  exact Nat.findGreatest_spec (P := fun m => axisSite m ∈ cluster 2 ω (origin 2))
    (Nat.zero_le R) (axisSite_zero_mem_cluster (ω := ω))


theorem fdc_rightExitIdx_is_greatest (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    {k : ℕ} (h1 : fdc_rightExitIdx (ω := ω) hfin R < k) (h2 : k ≤ R) :
    axisSite k ∉ cluster 2 ω (origin 2) := by
  classical
  rw [fdc_rightExitIdx] at h1
  exact Nat.findGreatest_is_greatest h1 h2


theorem fdc_rightExitIdx_succ_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) ∉ cluster 2 ω (origin 2) := by
  set m := fdc_rightExitIdx (ω := ω) hfin R with hm
  rcases lt_or_eq_of_le (fdc_rightExitIdx_le (ω := ω) hfin R) with hlt | heq
  · 
    exact fdc_rightExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · 
    have hmR : m = R := heq
    have hext : (axisSite (m + 1) : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < ((m : ℤ) + 1).natAbs
      rw [show ((m:ℤ)+1).natAbs = m + 1 by rw [Int.natAbs_eq_iff]; left; push_cast; ring]
      omega
    exact exterior_subset_compl _ R hR hext


theorem fdc_axis_reach (K : Set (Site 2)) (a j : ℕ)
    (hout : ∀ k, a ≤ k → k ≤ a + j → (axisSite k : Site 2) ∉ K) :
    ((hypercubicLattice 2).induce Kᶜ).Reachable
      ⟨axisSite a, hout a le_rfl (by omega)⟩
      ⟨axisSite (a + j), hout (a + j) (by omega) le_rfl⟩ := by
  induction j with
  | zero => exact Reachable.refl _
  | succ n ih =>
    have hout' : ∀ k, a ≤ k → k ≤ a + n → (axisSite k : Site 2) ∉ K := by
      intro k h1 h2; exact hout k h1 (by omega)
    have h1 := ih hout'
    have hk1 : (axisSite (a + n) : Site 2) ∉ K := hout (a + n) (by omega) (by omega)
    have hk2 : (axisSite (a + n + 1) : Site 2) ∉ K := hout (a + n + 1) (by omega) (by omega)
    have hdiff : unitWt ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) = 1 := by
      unfold unitWt
      rw [Fin.sum_univ_two]
      have e0 : ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) 0 = -1 := by
        simp [axisSite, Pi.sub_apply]
      have e1 : ((axisSite (a + n) : Site 2) - axisSite (a + n + 1)) 1 = 0 := by
        simp [axisSite, Pi.sub_apply]
      rw [e0, e1]; rfl
    have hstep := complReachable_of_unitDiff K hk1 hk2 hdiff
    have heq : (axisSite (a + n + 1) : Site 2) = axisSite (a + (n + 1)) := by
      have : a + n + 1 = a + (n + 1) := by omega
      rw [this]
    exact complReachable_congr (G := hypercubicLattice 2) (S := Kᶜ) rfl heq (h1.trans hstep)


theorem fdc_rightExit_adj (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (hypercubicLattice 2).Adj (axisSite (fdc_rightExitIdx (ω := ω) hfin R))
      (axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1)) := by
  set m := fdc_rightExitIdx (ω := ω) hfin R
  have hsucc : (axisSite (m + 1) : Site 2) = ![(m : ℤ) + 1, 0] := by
    funext i; fin_cases i <;> simp [axisSite]
  rw [show (axisSite m : Site 2) = ![(m : ℤ), 0] from rfl, hsucc]
  exact latAdj_right (m : ℤ) 0


end Percolation
end StatMech
