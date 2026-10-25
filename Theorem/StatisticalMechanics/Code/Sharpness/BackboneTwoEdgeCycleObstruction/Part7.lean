/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeCycleObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeBondToggle.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part7
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneTwoEdgeCycleObstruction

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneTwoEdgeBondProgram

open BackboneTwoEdgeBondToggle

open FluxEdgeCopy

attribute [simp] headEdge_ne_suffixEdge headEdge_ne_cycleEdge₀
  headEdge_ne_cycleEdge₁ headEdge_ne_cycleEdge₂
  suffixEdge_ne_cycleEdge₀ suffixEdge_ne_cycleEdge₁
  suffixEdge_ne_cycleEdge₂ cycleEdge₀_ne_cycleEdge₁
  cycleEdge₀_ne_cycleEdge₂ cycleEdge₁_ne_cycleEdge₂
  suffixEdge_ne_headEdge cycleEdge₀_ne_headEdge cycleEdge₁_ne_headEdge
  cycleEdge₂_ne_headEdge cycleEdge₀_ne_suffixEdge
  cycleEdge₁_ne_suffixEdge cycleEdge₂_ne_suffixEdge
  cycleEdge₁_ne_cycleEdge₀ cycleEdge₂_ne_cycleEdge₀
  cycleEdge₂_ne_cycleEdge₁


theorem extendFlux_restrictResidual
    (p : domain.graph.edgeFinset → Nat) (hp : p headEdge = 0) :
    extendFlux residualLe (restrictResidual p) = p := by
  funext e
  by_cases he : e = headEdge
  · subst e
    rw [show extendFlux residualLe (restrictResidual p) headEdge = 0 by
      unfold extendFlux
      rw [dif_neg (firstEdge_not_mem_delete domain headEdge)]]
    exact hp.symm
  · have hmem : e.1 ∈ residualGraph.edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.edgeSet_deleteEdges,
        canonicalEdgeSegment_edgeSet]
      refine ⟨SimpleGraph.mem_edgeFinset.mp e.2, ?_⟩
      simpa only [Set.mem_singleton_iff, Subtype.ext_iff] using he
    unfold extendFlux
    rw [dif_pos hmem]
    rfl

end BackboneTwoEdgeCycleObstruction
end
end StatMech.Sharpness
