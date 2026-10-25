/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def BalancedRepairAdmissible (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c : ↑m -> Fin 4) (Y : Finset ι) : Prop :=
  Y ⊆ outerMask m c ∧
    sources ends Y = ∅ ∧
    RowsDisconnect ends m c k zero ∧
    RowsDisconnect ends m (balancedSwap m X Y c) k zero


noncomputable def balancedRepairs (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c : ↑m -> Fin 4) : Finset (Finset ι) :=
  (outerMask m c).powerset.filter
    (fun Y => sources ends Y = ∅ ∧
      RowsDisconnect ends m c k zero ∧
      RowsDisconnect ends m (balancedSwap m X Y c) k zero)

end StatMech.GrahamGHS.FourColor
