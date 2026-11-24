module
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle.Part5
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalCollisionSquare
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferMatching.Part16
public import Theorem.StatisticalMechanics.Code.FrontierA.GrahamGateDiscrepancy.Part15
public import Abbrev.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal
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


noncomputable def sourceMaskCycleAction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (z : sourceMaskCycleSpace ends p) :
    leftSourceMaskFiber ends m j k l zero p :=
  sourceMaskCycleTranslationEquiv ends m j k l zero p z.1.1 z.2.1
    z.1.2.1 z.2.2.1 z.1.2.2 z.2.2.2 c


end StatMech.GrahamGHS.FourColor
