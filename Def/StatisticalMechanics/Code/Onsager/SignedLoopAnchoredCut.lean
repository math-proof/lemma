/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeMultibondAdapter.Part2
open scoped BigOperators
open Finset


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

variable {I P V : Type*}


def ons_optionAnchoredEquiv [DecidableEq I] :
    (I → Bool) ≃ AnchoredConfig (Option I) none where
  toFun tau := ⟨fun x => match x with
    | none => false
    | some i => !(tau i), rfl⟩
  invFun config := fun i => !(config.1 (some i))
  left_inv tau := by
    funext i
    simp
  right_inv config := by
    apply Subtype.ext
    funext x
    cases x with
    | none => simpa using config.2
    | some i => simp


end
end StatMech.Onsager
