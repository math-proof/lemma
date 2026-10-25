/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeUnitPacking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeSupportTag.Part2
import Instance.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking
open Finset


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def rightRowDataIndexFiber
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (R : rightRowSupportIndex ends m j k l zero) :=
  {d : rightRowData ends m j k l zero // d.1 = R}

end StatMech.GrahamGHS.FourColor
