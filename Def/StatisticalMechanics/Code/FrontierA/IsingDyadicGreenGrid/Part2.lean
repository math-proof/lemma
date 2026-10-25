/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingDyadicGreenGrid.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredContinuumGreen.Part2
import Mathlib.Data.ZMod.ValMinAbs
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenGrid
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {d k : Nat}


def isingNormalizedMomentumCube (d : Nat) : Set (IsingMomentumSpace d) :=
  {q | ∀ i, (-1 / 2 : Real) < q i ∧ q i ≤ 1 / 2}


def isingTorusLowMomentum (d k M : Nat) :
    Finset (IsingDyadicTorus d k) :=
  Finset.univ.filter fun p =>
    p ≠ 0 ∧ ∀ i : Fin d, (p i).valMinAbs.natAbs ≤ M

end StatMech.FrontierA
