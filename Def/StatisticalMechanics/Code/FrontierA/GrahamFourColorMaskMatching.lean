/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorMaskMatching.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorMaskMatching
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


noncomputable def maskFiberMatchedRight
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) : ↑m -> Fin 4 :=
  (f p c).1.1


end StatMech.GrahamGHS.FourColor
