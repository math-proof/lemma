/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part2
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


noncomputable def outsideCopies
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S : Finset (FluxEdgeCopy.Copy G m)) : Finset (FluxEdgeCopy.Copy G m) := by
  classical
  exact S.filter (fun i => endsM G m i ∉ cut)


def SupportedInCut
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (P : Finset (FluxEdgeCopy.Copy G m)) : Prop :=
  ∀ i ∈ P, endsM G m i ∈ cut


end BackboneDeterminedCutSwitching
end
end StatMech.Sharpness
