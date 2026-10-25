/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneP2CoordinateToggleObstruction
import Instance.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelector.Part2
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


theorem completeEvent_fluxEventOutsideCut
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V))
    (x : P.State) (accepted : Sym2 V)
    (hstate : P.initial d = P.scan.advance x accepted)
    (hfresh : SuffixFresh P.scan x accepted (P.encode d word))
    (m : d.graph.edgeFinset -> Nat)
    (hterminal : FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.TerminalEvent d word)) :
    FluxEventOutsideCut d.graph m
      ((P.scan.bondwiseOrdered.tests x).determinedCut accepted)
      (P.CompleteEvent d word) := by
  intro T U hout
  have hevent := bondwiseSuffixEvent_fluxEventOutsideCut d.graph P.scan x
    accepted (P.encode d word) hfresh P.bit m T U hout
  have hterminalEvent := hterminal T U hout
  constructor
  · rintro ⟨hselect, hterminal⟩
    refine ⟨?_, hterminalEvent.mp hterminal⟩
    have hresult := hevent.mp (by simpa [hstate] using hselect)
    simpa [hstate] using hresult
  · rintro ⟨hselect, hterminal⟩
    refine ⟨?_, hterminalEvent.mpr hterminal⟩
    have hresult := hevent.mpr (by simpa [hstate] using hselect)
    simpa [hstate] using hresult


end BackboneConcreteSelector
end
end StatMech.Sharpness
