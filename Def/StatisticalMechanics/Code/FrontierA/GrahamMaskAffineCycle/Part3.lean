/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskAffineCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamRowDataMaskHall.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskAffineCycle.Part3
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def rightMaskCycleTranslate
    (m : Finset I) (c d q : ↑m → Fin 4) : ↑m → Fin 4 :=
  balancedSwap m (balancedMiddleDifference m c d)
    (balancedOuterDifference m c d) q


end StatMech.GrahamGHS.FourColor
