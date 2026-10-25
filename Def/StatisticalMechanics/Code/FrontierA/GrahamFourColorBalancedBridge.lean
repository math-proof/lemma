/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamLemmaOneFourColor
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def grahamToBalancedColor (U : Finset ι) (q : GrahamFourColoring ι) :
    ↑U -> Fin 4 := fun x =>
  if (x : ι) ∈ q.color1 then 0
  else if (x : ι) ∈ q.color2 then 1
  else if (x : ι) ∈ q.color3 then 2
  else 3

end StatMech.FrontierA
