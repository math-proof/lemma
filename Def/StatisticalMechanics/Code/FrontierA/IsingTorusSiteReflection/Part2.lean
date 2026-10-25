/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part2
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusOnSitePlane (i : Fin d) (x : IsingDyadicTorus d k) : Prop :=
  (x i).val = 0 ∨ (x i).val = 2 ^ (k + 1)


def isingTorusInStrictLower (i : Fin d) (x : IsingDyadicTorus d k) : Prop :=
  0 < (x i).val ∧ (x i).val < 2 ^ (k + 1)

end StatMech.FrontierA
