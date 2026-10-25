/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneTwoEdgeExhaustiveProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeCycleObstruction.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneTwoEdgeExhaustiveProgram.Part3
open SimpleGraph Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneTwoEdgeExhaustiveProgram

open BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

open BackboneLabeledSwitching

open BackboneP2CoordinateReindex

open FluxEdgeCopy

namespace Cycle

open BackboneTwoEdgeCycleObstruction


@[simp] theorem oddTrianglePairFlux_cycle₀ :
    oddTrianglePairFlux cycleEdge₀ = 1 := by
  unfold oddTrianglePairFlux BackboneTwoEdgeBondProgram.twoUnitFlux unitFlux
  rw [oddCycleFlux_cycle₀]
  change ((if cycleEdge₀ = headEdge then 1 else 0) +
    (if cycleEdge₀ = suffixEdge then 1 else 0)) + 1 = 1
  rw [if_neg cycleEdge₀_ne_headEdge, if_neg cycleEdge₀_ne_suffixEdge]

@[simp] theorem oddTrianglePairBit_cycle₀ :
    fluxBitConfig domain.graph oddBit oddTrianglePairFlux cycleEdge₀.1 =
      true := by
  unfold fluxBitConfig
  simp [oddTrianglePairFlux_cycle₀, oddBit]


theorem not_noFurtherOdd_oddTrianglePair :
    ¬NoFurtherOdd
      (⟨domain, [headEdge.1, suffixEdge.1]⟩ :
        BackboneTwoEdgeBondProgram.State (Fin 6))
      headEdge.1 suffixEdge.1
      (fluxBitConfig domain.graph oddBit oddTrianglePairFlux) := by
  intro h
  have hfalse := h cycleEdge₀.1 cycleEdge₀.2
    (fun heq => cycleEdge₀_ne_headEdge (Subtype.ext heq))
    (fun heq => cycleEdge₀_ne_suffixEdge (Subtype.ext heq))
  rw [oddTrianglePairBit_cycle₀] at hfalse
  simp at hfalse


theorem not_program_complete_oddTrianglePair :
    ¬program.CompleteEvent domain
      [canonicalEdgeSegment domain.graph headEdge,
        canonicalEdgeSegment domain.graph suffixEdge]
      oddTrianglePairFlux := by
  intro hcomplete
  apply not_noFurtherOdd_oddTrianglePair
  exact noFurtherOdd_of_complete_canonical_pair domain headEdge suffixEdge
    oddTrianglePairFlux hcomplete


theorem not_selectorSpec_fiber_oddTrianglePair :
    ¬(selectorSpec (V := Fin 6)).toPartialSelector.Fiber domain
      [canonicalEdgeSegment domain.graph headEdge,
        canonicalEdgeSegment domain.graph suffixEdge]
      oddTrianglePairFlux := by
  rw [(selectorSpec (V := Fin 6)).fiber_iff_completeEvent]
  exact not_program_complete_oddTrianglePair

end Cycle
end BackboneTwoEdgeExhaustiveProgram
end
end StatMech.Sharpness
