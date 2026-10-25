/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OeisA211417_supercongruence_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


namespace OeisA211417

def a (n : ℕ) : ℕ :=
  (Nat.factorial (30 * n) * Nat.factorial n) /
  (Nat.factorial (15 * n) * Nat.factorial (10 * n) * Nat.factorial (6 * n))

open Nat Int Finset

def unitProd (p n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, if p ∣ i + 1 then 1 else i + 1

def unitIndex (p k : ℕ) := {i : Fin (p ^ k) // ¬p ∣ i.val}

end OeisA211417
