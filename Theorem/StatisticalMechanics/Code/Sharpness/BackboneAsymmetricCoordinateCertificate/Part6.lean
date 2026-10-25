/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneAsymmetricCoordinateCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneConcreteSelectorObstruction
import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part8
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


@[simp] theorem BondwiseSegmentProgram.runSpec_event
    (P : BondwiseSegmentProgram V)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    (P.runSpec d word).Event d.graph m <-> P.CompleteEvent d word m := by
  apply and_congr Iff.rfl
  change P.terminal
      (P.scan.residual (P.initial d) (P.encode d word))
        (fun e => ((fluxOptionConfig d.graph m e).map P.bit).getD false) <->
    P.terminal (P.scan.residual (P.initial d) (P.encode d word))
      (fluxBitConfig d.graph P.bit m)
  apply iff_of_eq
  congr 1
  funext e
  by_cases he : e ∈ d.graph.edgeFinset <;>
    simp [fluxOptionConfig, fluxBitConfig, he]


theorem CompleteBondwiseSelectorSpec.fiber_iff_runSpec_event
    {P : BondwiseSegmentProgram V} (R : CompleteBondwiseSelectorSpec P)
    (d : shb_ExplorationDomain V)
    (word : List (shb_ExplorationSegment V))
    (m : d.graph.edgeFinset -> Nat) :
    R.toPartialSelector.Fiber d word m <->
      (P.runSpec d word).Event d.graph m := by
  exact (R.fiber_iff_completeEvent d word m).trans
    (P.runSpec_event d word m).symm


end BackboneConcreteSelector
end
end StatMech.Sharpness
