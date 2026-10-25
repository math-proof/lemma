/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorUniformMaskSelector.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


noncomputable def canonicalTransferSize (ends : ι -> Sym2 W)
    (m : Finset ι) (k zero : W) (c : ↑m -> Fin 4) : Nat :=
  #(canonicalMiddleTransfer ends m c k zero) +
    #(canonicalOuterTransfer ends m c k zero)

noncomputable def canonicalTransferUnion (ends : ι -> Sym2 W)
    (m : Finset ι) (k zero : W) (c : ↑m -> Fin 4) : Finset ι :=
  canonicalMiddleTransfer ends m c k zero ∪
    canonicalOuterTransfer ends m c k zero

end StatMech.GrahamGHS.FourColor
