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
import Def.StatisticalMechanics.Code.Percolation.FarDartContour.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem fdc_farExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farExitDart (ω := ω) hfin R).tail = axisSite (fdc_rightExitIdx (ω := ω) hfin R) := rfl

@[simp] theorem fdc_farExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ) :
    (fdc_farExitDart (ω := ω) hfin R).head = axisSite (fdc_rightExitIdx (ω := ω) hfin R + 1) := rfl


theorem fdc_farExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (fdc_farExitDart (ω := ω) hfin R) :=
  ⟨fdc_rightExitIdx_mem (ω := ω) hfin R, fdc_rightExitIdx_succ_not_mem (ω := ω) hfin R hR⟩


theorem fdc_rightRun_not_mem (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) {k : ℕ}
    (h1 : fdc_rightExitIdx (ω := ω) hfin R + 1 ≤ k) (h2 : k ≤ R + 1) :
    (axisSite k : Site 2) ∉ cluster 2 ω (origin 2) := by
  rcases lt_or_eq_of_le h2 with hlt | heq
  · 
    exact fdc_rightExitIdx_is_greatest (ω := ω) hfin R (by omega) (by omega)
  · 
    have hkR : k = R + 1 := heq
    have hext : (axisSite k : Site 2) ∈ exterior 2 R := by
      refine ⟨0, ?_⟩
      show R < ((k : ℤ)).natAbs
      rw [show ((k:ℤ)).natAbs = k by exact Int.natAbs_natCast k]
      omega
    exact exterior_subset_compl _ R hR hext


theorem fdc_farExitDart_head_reaches_axisFar (hfin : (cluster 2 ω (origin 2)).Finite) (R : ℕ)
    (hR : cluster 2 ω (origin 2) ⊆ box 2 R) :
    ((hypercubicLattice 2).induce (cluster 2 ω (origin 2))ᶜ).Reachable
      ⟨(fdc_farExitDart (ω := ω) hfin R).head,
        (fdc_farExitDart_isBoundaryDart (ω := ω) hfin R hR).2⟩
      ⟨axisSite (R + 1), fdc_rightRun_not_mem (ω := ω) hfin R hR
        (Nat.succ_le_succ (fdc_rightExitIdx_le (ω := ω) hfin R)) (le_refl _)⟩ := by
  set m := fdc_rightExitIdx (ω := ω) hfin R with hm
  have hmR : m ≤ R := fdc_rightExitIdx_le (ω := ω) hfin R
  
  have hout : ∀ k, m + 1 ≤ k → k ≤ (m + 1) + (R - m) → (axisSite k : Site 2)
      ∉ cluster 2 ω (origin 2) := by
    intro k hk1 hk2
    have hk2' : k ≤ R + 1 := by omega
    exact fdc_rightRun_not_mem (ω := ω) hfin R hR hk1 hk2'
  have hreach := fdc_axis_reach (cluster 2 ω (origin 2)) (m + 1) (R - m) hout
  
  have heq : (axisSite ((m + 1) + (R - m)) : Site 2) = axisSite (R + 1) := by
    have : (m + 1) + (R - m) = R + 1 := by
      have : m ≤ R := fdc_rightExitIdx_le (ω := ω) hfin R
      omega
    rw [this]
  exact complReachable_congr (G := hypercubicLattice 2) (S := (cluster 2 ω (origin 2))ᶜ)
    rfl heq hreach


end Percolation
end StatMech
