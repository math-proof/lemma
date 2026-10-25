/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbitNesting.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitPropagation.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbitNesting
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

def CanonicalMaskAdjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c d : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ->
    RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero)
          c.1.1) k zero ->
    ¬ RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero)
          d.1.1) k zero ->
      edgeComponent ends (rowClass m d.1.1 0) zero ∪
          edgeComponent ends (rowClass m d.1.1 1) k ⊆
        edgeComponent ends (rowClass m r.1.1 0) zero ∪
          edgeComponent ends (rowClass m r.1.1 1) k


end StatMech.GrahamGHS.FourColor
