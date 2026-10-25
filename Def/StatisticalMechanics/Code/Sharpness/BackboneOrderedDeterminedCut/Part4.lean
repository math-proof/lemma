/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part3
open Finset BigOperators
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def FluxEventOutsideCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (Q : (G.edgeFinset -> Nat) -> Prop) : Prop :=
  ∀ S T : Finset (FluxEdgeCopy.Copy G m),
    outsideCopies G m cut S = outsideCopies G m cut T ->
      (Q (profileFlux G m S) <-> Q (profileFlux G m T))


end BackboneDeterminedCutSwitching
end
end StatMech.Sharpness
