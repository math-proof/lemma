/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneConcreteBondProgram.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneAsymmetricCoordinateCertificate.Part13
import Abbrev.StatisticalMechanics.Code.Sharpness.BackboneConcreteBondProgram.Part2
open SimpleGraph Finset

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

namespace BackboneConcreteBondProgram

open BackboneConcreteSelector

open BackboneDeterminedCutSwitching

theorem intendedOneStepRealization_isEmpty_of_noncanonical_chosen
    (d : shb_ExplorationDomain V) (m : d.graph.edgeFinset -> Nat)
    (s : shb_ExplorationSegment V)
    (hsrc : sources d.graph (ofEdgeFun d.graph m) ≠ ∅)
    (hchosen : shb_oneStepChosenSegment d m = some s)
    (hnoncanonical : ∀ e : d.graph.edgeFinset,
      canonicalEdgeSegment d.graph e ≠ s) :
    IsEmpty (IntendedOneStepRealization (V := V)) := by
  constructor
  intro R
  have hfiber : shb_oneStepPartialSelector.Fiber d [s] m := by
    unfold shb_PartialCurrentDynamicSelector.Fiber
    change (if sources d.graph (ofEdgeFun d.graph m) = ∅ then some []
      else (shb_oneStepChosenSegment d m).map (fun t => [t])) = some [s]
    rw [if_neg hsrc, hchosen]
    rfl
  have hcomplete := (R.complete_iff_fiber d [s] m).mpr hfiber
  obtain ⟨e, hsegment, _, _⟩ :=
    program_complete_singleton_data d m s hcomplete
  exact hnoncanonical e hsegment


end BackboneConcreteBondProgram
end
end StatMech.Sharpness
