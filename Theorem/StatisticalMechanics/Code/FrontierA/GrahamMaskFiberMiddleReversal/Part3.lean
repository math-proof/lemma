/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem rowsDisconnect_iff_bipartitionDisconnects
    (ends : I -> Sym2 W) (m : Finset I) (c : ↑m -> Fin 4)
    (u v : W) :
    RowsDisconnect ends m c u v ↔
      BipartitionDisconnects ends m (rowClass m c 0) u v := by
  rw [RowsDisconnect, BipartitionDisconnects, rowClass_one_eq_sdiff]


theorem reversalGateBalance_eq_bipartitionIndicators
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    reversalGateBalance ends m j k l zero p c =
      bipartitionDisconnectIndicator ends m
          (rowClass m c.1 0 ∆ p.1) k zero -
        bipartitionDisconnectIndicator ends m (rowClass m c.1 0) k zero := by
  classical
  unfold reversalGateBalance bipartitionDisconnectIndicator
  rw [rowsDisconnect_iff_bipartitionDisconnects,
    rowsDisconnect_iff_bipartitionDisconnects,
    rowClass_middleSwap_zero_eq_symmDiff_middleMask,
    show middleMask m c.1 = p.1 from congrArg Prod.fst c.2.2]


end StatMech.GrahamGHS.FourColor
