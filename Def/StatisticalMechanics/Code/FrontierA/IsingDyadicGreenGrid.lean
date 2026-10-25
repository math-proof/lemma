/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Mathlib.Data.ZMod.ValMinAbs
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {d k : Nat}


def isingDyadicSide (k : Nat) : Nat := 2 ^ (k + 2)


def isingTorusCenteredIntMomentum
    (p : IsingDyadicTorus d k) : Fin d → Int :=
  fun i => (p i).valMinAbs


noncomputable def isingTorusCenteredMomentum
    (p : IsingDyadicTorus d k) : IsingMomentumSpace d :=
  WithLp.toLp 2 fun i => ((p i).valMinAbs : Real) / isingDyadicSide k


noncomputable def isingTorusCenteredMomentumFun
    (p : IsingDyadicTorus d k) : Fin d → Real :=
  fun i => ((p i).valMinAbs : Real) / isingDyadicSide k

end StatMech.FrontierA
