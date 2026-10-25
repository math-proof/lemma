/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


abbrev MaskFiberEmbeddings (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) :=
  forall p : Finset I × Finset I,
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p


end StatMech.GrahamGHS.FourColor
