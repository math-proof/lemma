/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCoordinateSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusShellEmbedding
open Finset


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Lattice StatMech.Sharpness

variable {d k : Nat}


def isingTorusCoordinateSwap (i j : Fin d) :
    IsingDyadicTorus d k ≃ IsingDyadicTorus d k where
  toFun x a := x (Equiv.swap i j a)
  invFun x a := x (Equiv.swap i j a)
  left_inv x := by
    funext a
    change x (Equiv.swap i j (Equiv.swap i j a)) = x a
    rw [Equiv.swap_apply_self]
  right_inv x := by
    funext a
    change x (Equiv.swap i j (Equiv.swap i j a)) = x a
    rw [Equiv.swap_apply_self]

end StatMech.FrontierA
