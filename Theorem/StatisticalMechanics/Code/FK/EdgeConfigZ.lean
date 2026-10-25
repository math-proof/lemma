/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeConfigZ.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.SuperMultiplicative.Part4
import Theorem.StatisticalMechanics.Code.FK.FKInterfaceSubadd.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
open scoped BigOperators
open SimpleGraph Filter Topology Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


section Weight

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in


theorem ecz_openSub_eq_of_edges (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    openSub G ω₁ = openSub G ω₂ := by
  apply SimpleGraph.ext; ext x y; simp only [openSub_adj]
  constructor
  · rintro ⟨hadj, hop⟩
    exact ⟨hadj, by rw [← h s(x,y) (by rw [mem_edgeFinset]; exact hadj)]; exact hop⟩
  · rintro ⟨hadj, hop⟩
    exact ⟨hadj, by rw [h s(x,y) (by rw [mem_edgeFinset]; exact hadj)]; exact hop⟩


theorem ecz_numClusters_eq_of_edges (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    numClusters G ω₁ = numClusters G ω₂ := by
  unfold numClusters
  exact Fintype.card_congr (by rw [ecz_openSub_eq_of_edges G ω₁ ω₂ h])


theorem ecz_fkWeight_eq_of_edges (p q : ℝ) (ω₁ ω₂ : ConfigSpace (Sym2 V))
    (h : ∀ e ∈ G.edgeFinset, ω₁ e = ω₂ e) :
    fkWeight G p q ω₁ = fkWeight G p q ω₂ := by
  unfold fkWeight
  rw [ecz_numClusters_eq_of_edges G ω₁ ω₂ h]
  congr 1
  unfold edgeProduct
  exact Finset.prod_congr rfl (fun e he => by rw [h e he])

end Weight
end FK
end StatMech
