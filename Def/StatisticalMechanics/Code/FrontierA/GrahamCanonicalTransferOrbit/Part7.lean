/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalTransferOrbit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorCollisionStableSelector
import Mathlib.Data.Prod.Lex
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferOrbit.Part6
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskOrbitLocalDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c d : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p c d ->
    ¬ RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m c.1.1 k zero)
          (canonicalOuterTransfer ends m c.1.1 k zero)
          d.1.1) k zero ->
      canonicalTransferSize ends m k zero d.1.1 <
        canonicalTransferSize ends m k zero c.1.1


end StatMech.GrahamGHS.FourColor
