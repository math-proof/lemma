/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

noncomputable def shb_vacuumPartialSelector :
    shb_PartialCurrentDynamicSelector (V := V) where
  sourceClass := fun _ _ => ∅
  select? := fun d m =>
    if sources d.graph (ofEdgeFun d.graph m) = ∅ then some [] else none
  sourceClass_nil := by simp
  sources_eq_sourceClass_of_select := by
    intro d m word h
    split at h
    · rename_i hs
      simpa using hs
    · simp at h
  select?_eq_some_nil_iff := by
    intro d m
    split
    · rename_i hs
      simp [hs]
    · rename_i hs
      simp [hs]
  head_active_of_select := by
    intro d m s ss h
    split at h <;> simp at h

end
end StatMech.Sharpness
