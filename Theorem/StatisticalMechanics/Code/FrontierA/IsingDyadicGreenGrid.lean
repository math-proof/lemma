/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Mathlib.Data.ZMod.ValMinAbs
import Def.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenGrid
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {d k : Nat}


@[simp] theorem isingTorusCenteredMomentum_apply
    (p : IsingDyadicTorus d k) (i : Fin d) :
    isingTorusCenteredMomentum p i =
      ((p i).valMinAbs : Real) / isingDyadicSide k := rfl

@[simp] theorem isingTorusCenteredMomentumFun_apply
    (p : IsingDyadicTorus d k) (i : Fin d) :
    isingTorusCenteredMomentumFun p i =
      ((p i).valMinAbs : Real) / isingDyadicSide k := rfl


end StatMech.FrontierA
