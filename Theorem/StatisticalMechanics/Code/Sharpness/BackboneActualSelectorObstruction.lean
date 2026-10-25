/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorObstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorObstruction
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_singleEdgeGraph_edge_mem {x y : V} (hxy : x ≠ y) :
    s(x, y) ∈ (shb_singleEdgeGraph x y).edgeFinset := by
  rw [SimpleGraph.mem_edgeFinset, shb_singleEdgeGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  exact ⟨Set.mem_singleton _, by
    simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using hxy⟩

theorem shb_singleEdgeGraph_edgeFinset {x y : V} (hxy : x ≠ y) :
    (shb_singleEdgeGraph x y).edgeFinset = {s(x, y)} := by
  ext e
  rw [SimpleGraph.mem_edgeFinset, shb_singleEdgeGraph,
    SimpleGraph.edgeSet_fromEdgeSet]
  simp only [Set.mem_diff, Set.mem_singleton_iff, Finset.mem_singleton]
  constructor
  · exact And.left
  · intro he
    subst e
    exact ⟨rfl, by simpa [Sym2.mem_diagSet, Sym2.mk_isDiag_iff] using hxy⟩


end
end StatMech.Sharpness
