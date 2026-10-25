/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorus_side_eq_two_mul_half :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring


end StatMech.FrontierA
