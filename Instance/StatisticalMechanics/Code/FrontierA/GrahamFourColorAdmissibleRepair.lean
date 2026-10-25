/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part4
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


noncomputable instance instFintypeLeftMaskFiber
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι) :
    Fintype (leftMaskFiber ends m j k l zero p) := by
  classical
  unfold leftMaskFiber
  infer_instance

noncomputable instance instFintypeRightMaskFiber
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι) :
    Fintype (rightMaskFiber ends m j k l zero p) := by
  classical
  unfold rightMaskFiber
  infer_instance

end StatMech.GrahamGHS.FourColor
