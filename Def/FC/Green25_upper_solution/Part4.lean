/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/Green25_upper_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.FC.Green25_upper_solution.Part3
open Asymptotics Filter Finset


namespace Green25

def vectorKey (Q m r : ℕ) [NeZero (Q ^ m)] (x : ℕ) : Fin m → ℕ := fun i =>
  if i.1 < r then complementKey Q (digitVector Q m x i) else digitVector Q m x i

def flipVector (Q r : ℕ) {m : ℕ} (v : Fin m → Fin Q)
    (b : Fin r → Bool) : Fin m → Fin Q := fun i =>
  if h : i.1 < r then
    if b ⟨i, h⟩ then ⟨Q - 1 - v i, by have := (v i).isLt; omega⟩ else v i
  else v i


end Green25
