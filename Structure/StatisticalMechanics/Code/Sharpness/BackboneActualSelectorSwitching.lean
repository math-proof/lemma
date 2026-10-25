/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneActualSelectorSwitching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching
open SimpleGraph Finset
open scoped BigOperators

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

structure shb_CurrentDynamicSelector where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  select : (d : shb_ExplorationDomain V) ->
    (d.graph.edgeFinset -> Nat) -> List (shb_ExplorationSegment V)
  sourceClass_nil : forall d, sourceClass d [] = ∅
  sources_eq_sourceClass_of_select : forall d m word,
    select d m = word ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  select_nil_of_sources_empty : forall d m,
    sources d.graph (ofEdgeFun d.graph m) = ∅ -> select d m = []
  select_ne_cons_of_not_active : forall d s ss m,
    s ∉ d.active -> select d m ≠ s :: ss


end
end StatMech.Sharpness
