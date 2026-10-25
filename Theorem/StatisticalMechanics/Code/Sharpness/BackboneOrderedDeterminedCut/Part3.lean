/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePartialEdgeCopySwitching.Part6
import Def.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part3
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


theorem outsideCopies_symmDiff_eq
    (m : G.edgeFinset -> Nat) (cut : Set (Sym2 V))
    (S P : Finset (FluxEdgeCopy.Copy G m))
    (hP : SupportedInCut G m cut P) :
    outsideCopies G m cut (S ∆ P) = outsideCopies G m cut S := by
  classical
  ext i
  by_cases hi : endsM G m i ∈ cut
  · simp [outsideCopies, hi]
  · have hiP : i ∉ P := by
      intro hip
      exact hi (hP i hip)
    simp [outsideCopies, hi, hiP, Finset.mem_symmDiff]


end BackboneDeterminedCutSwitching
end
end StatMech.Sharpness
