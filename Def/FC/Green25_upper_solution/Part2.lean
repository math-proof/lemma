/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution
open Asymptotics Filter Finset


namespace Green25

def complementKey (Q a : ℕ) : ℕ := min a (Q - 1 - a)


def digitKey (Q r : ℕ) (L : List ℕ) : List ℕ :=
  L.mapIdx fun i a => if i < r then complementKey Q a else a

end Green25
