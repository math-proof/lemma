/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc12core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc9core
import Theorem.StatisticalMechanics.Code.Percolation.CanonicalTrifCount.Part4
open Set SimpleGraph
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open MeasureTheory


namespace StatMech

namespace Walls

variable {d : ℕ}


theorem bc12_cluster_ne_of_not_connected {σ : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (h : ¬ Connected d σ a b) : cluster d σ a ≠ cluster d σ b := by
  intro heq
  exact h (mem_cluster.mp (heq ▸ self_mem_cluster σ b))


theorem bc12_openAdj_forceOpen {ω : ConfigSpace (Sym2 (Site d))} (W : Finset (Sym2 (Site d)))
    {a b : Site d} (h : (openSubgraph d ω).Adj a b) :
    (openSubgraph d (forceOpenFinset W ω)).Adj a b := by
  rw [openSubgraph_adj] at h ⊢
  refine ⟨h.1, ?_⟩
  have hle := forceOpenFinset_le W ω s(a, b)
  rw [h.2] at hle
  exact le_antisymm (by simp) hle


theorem bc12_canonicalTrif_discharges_boxReach (ω : ConfigSpace (Sym2 (Site d)))
    (htri : IsCanonicalTrifurcation d ω 0) :
    ∃ W : Finset (Sym2 (Site d)),
      (∀ e ∈ W, (0 : Site d) ∉ e) ∧
      ∃ y₁ y₂ y₃ : Site d,
        y₁ ≠ 0 ∧ y₂ ≠ 0 ∧ y₃ ≠ 0 ∧
        Connected d (forceOpenFinset W ω) 0 y₁ ∧
        Connected d (forceOpenFinset W ω) 0 y₂ ∧
        Connected d (forceOpenFinset W ω) 0 y₃ ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₁).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₂).Infinite ∧
        (cluster d (removeSite 0 (forceOpenFinset W ω)) y₃).Infinite ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₁ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ ∧
        cluster d (removeSite 0 (forceOpenFinset W ω)) y₂ ≠
          cluster d (removeSite 0 (forceOpenFinset W ω)) y₃ := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := htri
  
  exact bc9_boxOriginReach_of_reach ω
    ((openSubgraph d ω).ne_of_adj hadj.1).symm
    ((openSubgraph d ω).ne_of_adj hadj.2.1).symm
    ((openSubgraph d ω).ne_of_adj hadj.2.2).symm
    hadj.1.reachable hadj.2.1.reachable hadj.2.2.reachable
    hinf.1 hinf.2.1 hinf.2.2
    (bc12_cluster_ne_of_not_connected hsep.1)
    (bc12_cluster_ne_of_not_connected hsep.2.1)
    (bc12_cluster_ne_of_not_connected hsep.2.2)


end Walls
end StatMech
