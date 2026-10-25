/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

theorem shb_vacuumPartialSelector_admissible_iff
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat) :
    shb_vacuumPartialSelector.Admissible d m <->
      sources d.graph (ofEdgeFun d.graph m) = ∅ := by
  constructor
  · rintro ⟨word, hword⟩
    by_cases hs : sources d.graph (ofEdgeFun d.graph m) = ∅
    · exact hs
    · change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then
        some [] else none) = some word at hword
      simp [hs] at hword
  · intro hs
    exact ⟨[], by simp [shb_vacuumPartialSelector, hs]⟩


end
end StatMech.Sharpness
