/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackbonePartialEdgeCopySwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

structure shb_PartialCurrentDynamicSelector where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  select? : (d : shb_ExplorationDomain V) ->
    (d.graph.edgeFinset -> Nat) -> Option (List (shb_ExplorationSegment V))
  sourceClass_nil : forall d, sourceClass d [] = ∅
  sources_eq_sourceClass_of_select : forall d m word,
    select? d m = some word ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  select?_eq_some_nil_iff : forall d m,
    select? d m = some [] <->
      sources d.graph (ofEdgeFun d.graph m) = ∅
  head_active_of_select : forall d m s ss,
    select? d m = some (s :: ss) -> s ∈ d.active


end
end StatMech.Sharpness
