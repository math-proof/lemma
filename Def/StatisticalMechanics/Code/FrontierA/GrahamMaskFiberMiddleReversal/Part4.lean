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
import Instance.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part2
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def reversalGateBalance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) : ℤ :=
  by
    classical
    exact
      (if RowsDisconnect ends m (middleSwap m c.1) k zero then 1 else 0) -
        if RowsDisconnect ends m c.1 k zero then 1 else 0


def BipartitionDisconnects
    (ends : I -> Sym2 W) (m E : Finset I) (u v : W) : Prop :=
  ¬ connK ends E u v ∧ ¬ connK ends (m \ E) u v


noncomputable def bipartitionDisconnectIndicator
    (ends : I -> Sym2 W) (m E : Finset I) (u v : W) : ℤ := by
  classical
  exact if BipartitionDisconnects ends m E u v then 1 else 0

end StatMech.GrahamGHS.FourColor
