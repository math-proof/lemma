/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def componentExchangeSupportFiberEmbedding
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (R : rightRowSupportIndex ends m j k l zero) :
    componentExchangeSupportFiber ends m j k l zero R ↪
      rightRowDataIndexFiber ends m j k l zero R where
  toFun d := ⟨componentExchangeSupportTag ends m j k l zero
      hloop hjk hkl hk0 d.1, by
    apply Subtype.ext
    exact d.2⟩
  inj' := by
    intro d e hde
    apply Subtype.ext
    apply componentExchangeSupportTag_injective
      ends m j k l zero hloop hjk hkl hk0
    exact congrArg Subtype.val hde


end StatMech.GrahamGHS.FourColor
