/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking.Part3
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rightRowDataIndexFiber_card_eq_weight
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype.card (rightRowDataIndexFiber ends m j k l zero R) =
      rowSupportWeight ends m R.1 := by
  classical
  rw [Fintype.card_congr
    (rightRowDataIndexFiberEquiv ends m j k l zero R), Fintype.card_prod]
  rcases R.2.2.2.1 with ⟨P, hPsub, hPsrc⟩
  let hP : boundarySector ends R.1 {j, k} := ⟨P, hPsub, hPsrc⟩
  rw [boundarySector_card_eq_cycle ends R.1 {j, k} hP]
  rfl


end StatMech.GrahamGHS.FourColor
