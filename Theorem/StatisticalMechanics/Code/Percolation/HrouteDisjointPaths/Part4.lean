/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/HrouteDisjointPaths.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationConstruction.Part3
import Def.StatisticalMechanics.Code.Percolation.HrouteDisjointPaths.Part2
open MeasureTheory Set
open scoped ENNReal BigOperators
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

namespace DisjointPaths

variable {d : ℕ}


theorem corridorCover_of_routing {n : ℕ}
    (hroute : ∀ ω ∈ threeMeetBox d n, DisjointCorridorRouting ω) :
    threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G := by
  intro ω hω
  obtain ⟨a₁, a₂, a₃, G, w₁, w₂, w₃, S₁, S₂, S₃, hne, hadj, ⟨hc1, hc2, hc3⟩,
    ⟨hw1, hw2, hw3⟩, ⟨hm1, hm2, hm3⟩, ⟨hcl1, hcl2, hcl3⟩, ⟨hd12, hd13, hd23⟩⟩ := hroute ω hω
  have hworks : ω ∈ CorridorWorks a₁ a₂ a₃ G :=
    corridorWorks_of_corridors ω a₁ a₂ a₃ G hne hadj w₁ w₂ w₃ hc1 hc2 hc3 hw1 hw2 hw3
      S₁ S₂ S₃ hm1 hm2 hm3 hcl1 hcl2 hcl3 hd12 hd13 hd23
  simp only [Set.mem_iUnion]
  exact ⟨a₁, a₂, a₃, G, hworks⟩


theorem burton_keane_uniqueness_corridorCover
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hcorr : ∀ n : ℕ, threeMeetBox d n ⊆
      ⋃ (a₁ : Site d) (a₂ : Site d) (a₃ : Site d) (G : Finset (Sym2 (Site d))),
        CorridorWorks a₁ a₂ a₃ G) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_trif_route μ herg hfe bdry hbound hvol hdens
    (hroute_of_corridorCover μ hfe hcorr)


theorem burton_keane_uniqueness_disjointRouting
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ)
    (bdry : ℕ → ℕ)
    (hbound : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), Tcount d ω n ≤ bdry n)
    (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
    (hdens : Filter.Tendsto
      (fun n => (bdry n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (hroute : ∀ (n : ℕ) (ω : ConfigSpace (Sym2 (Site d))),
      ω ∈ threeMeetBox d n → DisjointCorridorRouting ω) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨ μ {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ μ (atLeastTwoInfinite d) = 0
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  burton_keane_uniqueness_corridorCover μ herg hfe bdry hbound hvol hdens
    (fun n => corridorCover_of_routing (fun ω hω => hroute n ω hω))

end DisjointPaths
end Percolation
end StatMech
