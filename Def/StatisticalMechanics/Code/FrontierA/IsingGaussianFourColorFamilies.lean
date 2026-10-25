/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorFamilies.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorSwitch.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedBridge.Part2
open Finset
open Classical


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


def FiniteTreeSeparatedBranchPattern
    (ends : ι -> Sym2 V) (U : Finset ι) (i j k l y : V)
    (c : ↑U -> Fin 4) : Prop :=
  FiniteTreeSeparatedSources ends U i j k l c ∧
    connK ends (colorClass U c 0 ∪ colorClass U c 1) i y ∧
    connK ends (colorClass U c 2 ∪ colorClass U c 3) k y


end StatMech.FrontierA
