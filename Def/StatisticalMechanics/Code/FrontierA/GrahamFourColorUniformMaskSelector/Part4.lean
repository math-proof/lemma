/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part3
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


noncomputable def uniformMaskCanonicalSelector
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (c : ↑m -> Fin 4) : Finset ι × Finset ι :=
  let r := leftMaskReference ends m j k l zero
    (fourColorMaskProfile m c)
  (canonicalMiddleTransfer ends m r k zero,
    canonicalOuterTransfer ends m r k zero)

end StatMech.GrahamGHS.FourColor
