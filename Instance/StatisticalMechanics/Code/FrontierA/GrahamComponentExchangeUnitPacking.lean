/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable instance instFintypeComponentExchangeSupportFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :
    Fintype (componentExchangeSupportFiber ends m j k l zero R) := by
  classical
  exact Fintype.subtype (Finset.univ.filter fun d =>
    exchangeFirstRow ends d.1 (m \ d.1) k zero = R.1) (by simp)


end StatMech.GrahamGHS.FourColor
