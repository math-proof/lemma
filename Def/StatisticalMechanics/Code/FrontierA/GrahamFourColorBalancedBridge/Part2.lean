/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def balancedColorToGraham (U : Finset ι) (c : ↑U -> Fin 4) :
    GrahamFourColoring ι where
  color1 := colorClass U c 0
  color2 := colorClass U c 1
  color3 := colorClass U c 2

end StatMech.FrontierA
