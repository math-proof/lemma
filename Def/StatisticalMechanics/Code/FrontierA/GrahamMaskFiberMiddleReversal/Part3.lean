module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part2
open Finset
open scoped symmDiff


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversal.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def leftSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    RowsDisconnect ends m c.1 k zero}


def reversedRightSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    RowsDisconnect ends m (middleSwap m c.1) k zero}

end StatMech.GrahamGHS.FourColor
