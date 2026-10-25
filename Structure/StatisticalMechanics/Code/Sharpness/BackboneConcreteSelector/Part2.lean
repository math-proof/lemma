/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector.Part2
open SimpleGraph Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackbonePartialP2Reindex

open BackboneP2CoordinateReindex

open BackboneP2CoordinateToggleObstruction

open FluxEdgeCopy

variable {D : Type*}


structure CompleteBondwiseSelectorSpec (P : BondwiseSegmentProgram V) where
  sourceClass : shb_ExplorationDomain V ->
    List (shb_ExplorationSegment V) -> Finset V
  sourceClass_nil : ∀ d, sourceClass d [] = ∅
  complete_functional : ∀ d m word word',
    P.CompleteEvent d word m -> P.CompleteEvent d word' m -> word = word'
  sources_eq_sourceClass_of_complete : ∀ d m word,
    P.CompleteEvent d word m ->
      sources d.graph (ofEdgeFun d.graph m) = sourceClass d word
  complete_nil_iff : ∀ d m,
    P.CompleteEvent d [] m ↔
      sources d.graph (ofEdgeFun d.graph m) = ∅
  head_active_of_complete : ∀ d m s ss,
    P.CompleteEvent d (s :: ss) m -> s ∈ d.active


end BackboneConcreteSelector
end
end StatMech.Sharpness
