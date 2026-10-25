/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/ClusterAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ClusterExplorationFreeBoundary
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Def.StatisticalMechanics.Code.FK.ClusterAdaptiveProjection
open SimpleGraph


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mem_clusterAdaptiveInsideEdges_iff (roots : Finset V)
    (rho : ConfigSpace (Sym2 V)) (e : Sym2 V) :
    e ∈ clusterAdaptiveInsideEdges G roots rho ↔
      ∃ x y : V, e = s(x, y) ∧
        ¬ ClusterExploredVertex G rho roots x ∧
        ¬ ClusterExploredVertex G rho roots y := by
  classical
  rw [clusterAdaptiveInsideEdges, clusterUnexploredPairEdges,
    ocd_mem_innerEdgeFinset]
  constructor
  · rintro ⟨edge, rfl⟩
    induction edge using Sym2.ind with
    | _ x y =>
        exact ⟨x.1, y.1, ocd_innerEdge_mk _ x y, x.2, y.2⟩
  · rintro ⟨x, y, rfl, hx, hy⟩
    let x' : ClusterUnexploredVertex G rho roots := ⟨x, hx⟩
    let y' : ClusterUnexploredVertex G rho roots := ⟨y, hy⟩
    exact ⟨s(x', y'), ocd_innerEdge_mk _ x' y'⟩


end
end StatMech.FK
