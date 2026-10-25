/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDualityObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part12
import Theorem.StatisticalMechanics.Code.FK.PcNontrivial.Part2
import Def.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDualityObstruction.Part6
open Set SimpleGraph
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

namespace SymmetricDomain

noncomputable section

theorem connectedRequiredEdges_subset :
    connectedRequiredEdges ⊆ connectedSymmetricDomain.finiteGraph.edgeFinset := by
  intro e he
  simp only [connectedRequiredEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · simpa only [SimpleGraph.mem_edgeFinset] using connected_adj_one_bridge
  · simpa only [SimpleGraph.mem_edgeFinset] using connected_adj_two_bridge

@[simp] theorem connectedRequiredEdges_card :
    connectedRequiredEdges.card = 2 := by
  simp [connectedRequiredEdges, connectedVertexOne, connectedVertexTwo,
    connectedVertexBridge, separatedSiteOne, separatedSiteTwo,
    connectedBridgeSite]


theorem connected_openConnectionProbability_eq_quarter :
    connectedSymmetricDomain.openConnectionProbability 1 = 1 / 4 := by
  have hsd : selfDualPoint 1 = (1 / 2 : Real) := by
    norm_num [selfDualPoint]
  unfold openConnectionProbability mixedMass
  rw [hsd]
  simp_rw [bcProb_one_eq_fkProb_one]
  calc
    (∑ omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex),
        if connectedSymmetricDomain.OpenConnected omega then
          FK.fkProb connectedSymmetricDomain.finiteGraph (1 / 2) 1 omega
        else 0) =
      ∑ omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex),
        (if (∀ e ∈ connectedRequiredEdges, omega e = true) then
          (1 : Real) else 0) *
          FK.fkProb connectedSymmetricDomain.finiteGraph (1 / 2) 1 omega := by
        apply Finset.sum_congr rfl
        intro omega _
        simp only [connected_openConnected_iff]
        simp [connectedRequiredEdges]
    _ = (1 / 2 : Real) ^ connectedRequiredEdges.card :=
      FK.fkProbOne_cylinder (G := connectedSymmetricDomain.finiteGraph)
        (by norm_num) (by norm_num) connectedRequiredEdges
        connectedRequiredEdges_subset
    _ = 1 / 4 := by norm_num


theorem connected_selfDuality_lower_bound_false :
    ¬(1 / (1 + (1 : Real) ^ 2) ≤
      connectedSymmetricDomain.openConnectionProbability 1) := by
  rw [connected_openConnectionProbability_eq_quarter]
  norm_num


theorem connected_mixedDualComplementRN_isEmpty :
    IsEmpty (MixedDualComplementRN connectedSymmetricDomain 1) := by
  constructor
  intro R
  apply connected_selfDuality_lower_bound_false
  exact openConnectionProbability_ge_one_div_one_add_q_sq
    connectedSymmetricDomain (by norm_num) R


theorem not_all_symmetricDomain_selfDuality_lower_bounds :
    ¬∀ D : SymmetricDomain,
      1 / (1 + (1 : Real) ^ 2) ≤ D.openConnectionProbability 1 := by
  intro hall
  exact separated_selfDuality_lower_bound_false (hall separatedSymmetricDomain)


theorem no_universal_mixedDualComplementRN (q : Real) :
    ¬∀ D : SymmetricDomain, Nonempty (MixedDualComplementRN D q) := by
  intro hall
  rcases hall separatedSymmetricDomain with ⟨R⟩
  exact (separated_mixedDualComplementRN_isEmpty q).false R

end
end SymmetricDomain
end BeffaraDC
end StatMech
