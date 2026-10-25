/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantMasks.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
open Finset
open Classical


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]

def middleMask (m : Finset ι) (c : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 1 ∪ colorClass m c 2

def outerMask (m : Finset ι) (c : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 0 ∪ colorClass m c 3

end StatMech.GrahamGHS.FourColor
