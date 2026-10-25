/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part2
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def balancedMiddleDifference (m : Finset ι) (c d : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 1 ∆ colorClass m d 1


def balancedOuterDifference (m : Finset ι) (c d : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 0 ∆ colorClass m d 0

end StatMech.GrahamGHS.FourColor
