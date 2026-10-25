/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexColoredStrandSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexColoredLoopPairing.Part16
import Def.StatisticalMechanics.Code.FrontierD.SixVertexColoredStrandSplice.Part4
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem card_boolFalseFiber
    {A : Type*} [Fintype A] (color : A -> Bool) :
    Fintype.card {x : A // color x = false} =
      Fintype.card A - Fintype.card {x : A // color x = true} := by
  rw [Fintype.card_congr (boolFalseFiberEquivComplementTrue color)]
  exact Fintype.card_subtype_compl (fun x => color x = true)


end
end StatMech.FrontierD
