/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTotalDisconnectedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRankOneGate
import Def.StatisticalMechanics.Code.FrontierA.GrahamTotalDisconnectedHall
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowDataRepairHall_of_total_disconnected
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hdisc : ¬ connK ends m k zero) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskFiberEmbeddings
  intro p
  exact totalDisconnectedMaskFiberEmbedding
    ends m j k l zero hdisc p

end StatMech.GrahamGHS.FourColor
