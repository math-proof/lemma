/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Instance.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def rightRowDataIndexFiberEquiv
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    rightRowDataIndexFiber ends m j k l zero R ≃
      boundarySector ends R.1 {j, k} × boundarySector ends (m \ R.1) ∅ where
  toFun d := d.2 ▸ d.1.2
  invFun p := ⟨⟨R, p⟩, rfl⟩
  left_inv d := by
    rcases d with ⟨⟨K, p⟩, hK⟩
    dsimp at hK ⊢
    subst K
    rfl
  right_inv p := rfl


end StatMech.GrahamGHS.FourColor
