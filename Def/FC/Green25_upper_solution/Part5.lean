/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part4
open Asymptotics Filter Finset


namespace Green25

def shift25 (a : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.image (a + ·)

end Green25
