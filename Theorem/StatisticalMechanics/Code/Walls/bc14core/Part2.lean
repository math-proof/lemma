/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc14core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc13core
import Theorem.StatisticalMechanics.Code.Percolation.ClusterReachesRay.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ClusterRunsAxisFE.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoxMergeFreeMenger.Part2
import Def.StatisticalMechanics.Code.Walls.bc14core
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc14_boxClusterReachesRay_of_runsAlong {n : ℕ}
    (h : bc14_BoxClusterRunsAlongAxis d n) : lma_BoxClusterReachesRay d n := by
  intro ω hω x₁ x₂ x₃ hb1 hb2 hb3 hi1 hi2 hi3 _hcd12 _hcd13 _hcd23
  obtain ⟨j₁, hr1⟩ := h ω hω x₁ hb1 hi1
  obtain ⟨j₂, hr2⟩ := h ω hω x₂ hb2 hi2
  obtain ⟨j₃, hr3⟩ := h ω hω x₃ hb3 hi3
  exact ⟨j₁, j₂, j₃,
    crr_clusterReachesRay_of_runsAlongAxis ω x₁ j₁ hr1,
    crr_clusterReachesRay_of_runsAlongAxis ω x₂ j₂ hr2,
    crr_clusterReachesRay_of_runsAlongAxis ω x₃ j₃ hr3⟩


theorem bc14_bc13BoxClusterReachesRay_of_runsAlong {n : ℕ}
    (h : bc14_BoxClusterRunsAlongAxis d n) : bc13_BoxClusterReachesRay d n :=
  bc14_boxClusterReachesRay_of_runsAlong h


theorem bc14_hroute_of_runsAlong
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : HasFiniteEnergyMerge μ)
    (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
    ∀ n : ℕ, 0 < μ (threeMeetBox d n) →
      ∃ a₁ a₂ a₃ : Site d, 0 < μ (NeighborTrifPrecursor d a₁ a₂ a₃) :=
  bc13_hroute_of_clusterReachesRay μ hfe
    (fun n => bc14_bc13BoxClusterReachesRay_of_runsAlong (hrun n))


theorem bc14_burton_keane_uniqueness_of_runsAlong
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hrun : ∀ n : ℕ, bc14_BoxClusterRunsAlongAxis d n) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc13_burton_keane_uniqueness_of_clusterReachesRay μ herg hfe bdry hbound hvol hdens
    (fun n => bc14_bc13BoxClusterReachesRay_of_runsAlong (hrun n))


theorem bc14_clusterRunsAlongAxis_neighbour (ω : ConfigSpace (Sym2 (Site d))) (j : Fin d)
    (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
    ∃ j' : Fin d, crr_ClusterRunsAlongAxis ω (hrHD_rayPt j 1) j' :=
  ⟨j, crr_runsAlongAxis_of_neighbour ω j hinf⟩


theorem bc14_boxClusterReachesRay_nonvacuous (ω : ConfigSpace (Sym2 (Site d)))
    (x₁ x₂ x₃ : Site d) (j₁ j₂ j₃ : Fin d)
    (hx1 : x₁ = hrHD_rayPt j₁ 1) (hx2 : x₂ = hrHD_rayPt j₂ 1) (hx3 : x₃ = hrHD_rayPt j₃ 1)
    (hi1 : (cluster d (removeSite 0 ω) x₁).Infinite)
    (hi2 : (cluster d (removeSite 0 ω) x₂).Infinite)
    (hi3 : (cluster d (removeSite 0 ω) x₃).Infinite) :
    ∃ j₁' j₂' j₃' : Fin d,
      lma_ClusterReachesRay ω x₁ j₁' ∧ lma_ClusterReachesRay ω x₂ j₂' ∧
        lma_ClusterReachesRay ω x₃ j₃' := by
  subst hx1 hx2 hx3
  refine ⟨j₁, j₂, j₃, ?_, ?_, ?_⟩
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₁ (crr_runsAlongAxis_of_neighbour ω j₁ hi1)
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₂ (crr_runsAlongAxis_of_neighbour ω j₂ hi2)
  · exact crr_clusterReachesRay_of_runsAlongAxis ω _ j₃ (crr_runsAlongAxis_of_neighbour ω j₃ hi3)


theorem bc14_runsAlong_arbitrary_omega_record (ω : ConfigSpace (Sym2 (Site d)))
    (x : Site d) (hinf : (cluster d ω x).Infinite) (n : ℕ) :
    ∃ y, (∃ i : Fin d, n < (y i).natAbs) ∧ Connected d ω x y :=
  craf_someAxis_reach_of_infinite ω x hinf n


end Walls
end StatMech
