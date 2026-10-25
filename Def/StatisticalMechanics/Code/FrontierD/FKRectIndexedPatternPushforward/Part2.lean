/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectIndexedPatternPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutPushforward.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightStripConnection.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectIndexedPatternPushforward
open Finset


namespace StatMech.FrontierD

noncomputable section

def FKRectDependsOnOutsideEdges (R : FKRectTorus)
    (I : Finset R.EdgeIndex) (B : Set R.Configuration) : Prop :=
  ∀ omega tau : R.Configuration,
    (∀ a ∉ I, omega a = tau a) → (omega ∈ B ↔ tau ∈ B)


end
end StatMech.FrontierD
