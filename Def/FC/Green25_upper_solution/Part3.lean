/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part2
open Asymptotics Filter Finset


namespace Green25

def digitVector (Q m x : ℕ) [NeZero (Q ^ m)] : Fin m → Fin Q :=
  finFunctionFinEquiv.symm (Fin.ofNat (Q ^ m) (x - 1))

def encodeVector {Q m : ℕ} (v : Fin m → Fin Q) : ℕ :=
  (finFunctionFinEquiv v : ℕ) + 1

end Green25
