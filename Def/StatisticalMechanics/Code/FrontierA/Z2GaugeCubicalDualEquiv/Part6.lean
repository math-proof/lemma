/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part5
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

def selectedOptionSpin {α : Type*} [DecidableEq α] (S : Finset α) :
    Option α → Bool
  | none => false
  | some q => decide (q ∈ S)


end
end StatMech.FrontierA
