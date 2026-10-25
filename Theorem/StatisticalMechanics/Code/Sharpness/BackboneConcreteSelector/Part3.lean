/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector.Part2
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


theorem CompleteBondwiseSelectorSpec.fiber_iff_completeEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    R.toPartialSelector.Fiber d word m <-> P.CompleteEvent d word m := by
  constructor
  · intro hfiber
    unfold shb_PartialCurrentDynamicSelector.Fiber at hfiber
    change R.select? d m = some word at hfiber
    unfold CompleteBondwiseSelectorSpec.select? at hfiber
    split at hfiber
    · rename_i hex
      have hchosen : Classical.choose hex = word := Option.some.inj hfiber
      exact hchosen ▸ Classical.choose_spec hex
    · simp at hfiber
  · intro hcomplete
    let hex : ∃ candidate, P.CompleteEvent d candidate m := ⟨word, hcomplete⟩
    unfold shb_PartialCurrentDynamicSelector.Fiber
    change R.select? d m = some word
    unfold CompleteBondwiseSelectorSpec.select?
    rw [dif_pos hex]
    apply congrArg some
    exact R.complete_functional d m
      (Classical.choose hex) word (Classical.choose_spec hex) hcomplete


theorem CompleteBondwiseSelectorSpec.fiber_iff_bondwiseSuffixEvent
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : P.TerminalEvent d word m) :
    R.toPartialSelector.Fiber d word m ↔
      BondwiseSuffixEvent d.graph P.scan (P.initial d)
        (P.encode d word) P.bit m := by
  rw [R.fiber_iff_completeEvent]
  simp [BondwiseSegmentProgram.CompleteEvent, hterminal]


theorem CompleteBondwiseSelectorSpec.fiber_fluxEventOutsideCut
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (x : P.State) (accepted : Sym2 V)
    (hstate : P.initial d = P.scan.advance x accepted)
    (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.TerminalEvent d word)) :
    FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (R.toPartialSelector.Fiber d word) := by
  intro T U hout
  rw [R.fiber_iff_completeEvent, R.fiber_iff_completeEvent]
  exact completeEvent_fluxEventOutsideCut P d word x accepted hstate hfresh
    m hterminal T U hout


end BackboneConcreteSelector
end
end StatMech.Sharpness
