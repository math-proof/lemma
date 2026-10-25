/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorAdmissibleRepair.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantMasks
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorAdmissibleRepair.Part3
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]


def fourColorMaskProfile (m : Finset ι) (c : ↑m -> Fin 4) :
    Finset ι × Finset ι :=
  (middleMask m c, outerMask m c)

def leftMaskFiber (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) :=
  {c : leftFiber ends m {j, k} {k, l} k zero //
    fourColorMaskProfile m c.1 = p}

def rightMaskFiber (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) :=
  {c : rightFiber ends m {j, k} {k, l} k zero //
    fourColorMaskProfile m c.1 = p}

end StatMech.GrahamGHS.FourColor
