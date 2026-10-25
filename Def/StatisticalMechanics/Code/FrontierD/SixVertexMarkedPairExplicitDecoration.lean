/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairExplicitDecoration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairCTypeHall.Part4
import Abbrev.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairExplicitDecoration.Part2
open Finset


namespace StatMech.FrontierD

noncomputable section

def sixVertexPairCTypeSiteEquivSum
    {T : EvenTorus} (omega eta : SixVertexArrows T) :
    SixVertexPairCTypeSite omega eta ≃
      {v : T.Vertex // omega.IsCType v} ⊕
        {v : T.Vertex // eta.IsCType v} where
  toFun x := if h : x.1.1 = false then
      Sum.inl ⟨x.1.2, by simpa [h] using x.2⟩
    else Sum.inr ⟨x.1.2, by
      have ht : x.1.1 = true := Bool.eq_true_of_not_eq_false h
      simpa [ht] using x.2⟩
  invFun x := match x with
    | Sum.inl v => ⟨(false, v.1), by simpa using v.2⟩
    | Sum.inr v => ⟨(true, v.1), by simpa using v.2⟩
  left_inv x := by
    rcases x with ⟨⟨layer, v⟩, hc⟩
    cases layer <;> simp
  right_inv x := by
    rcases x with v | v <;> simp

end
end StatMech.FrontierD
