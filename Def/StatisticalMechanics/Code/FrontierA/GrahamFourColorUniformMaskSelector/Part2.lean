/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def IsLeftMaskCandidate (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι)
    (c : ↑m -> Fin 4) : Prop :=
  LeftPattern ends m {j, k} {k, l} k zero c ∧
    fourColorMaskProfile m c = p

end StatMech.GrahamGHS.FourColor
