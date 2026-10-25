/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamTotalDisconnectedHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRankOneGate
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowsDisconnect_of_total_disconnected
    (ends : I → Sym2 W) (m : Finset I) (k zero : W)
    (hdisc : ¬ connK ends m k zero) (c : ↑m → Fin 4) :
    RowsDisconnect ends m c k zero := by
  constructor
  · intro h
    exact hdisc (connK_mono
      (Finset.union_subset (colorClass_subset m c 0)
        (colorClass_subset m c 1)) h)
  · intro h
    exact hdisc (connK_mono
      (Finset.union_subset (colorClass_subset m c 2)
        (colorClass_subset m c 3)) h)


end StatMech.GrahamGHS.FourColor
