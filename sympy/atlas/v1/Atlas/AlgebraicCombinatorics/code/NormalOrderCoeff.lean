/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/NormalOrderCoeff.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace NormalOrderCoeff

def normalOrderCoeff : ℕ → ℕ → ℕ → ℚ
  | i, j, 0 => if i = 0 ∧ j = 0 then 1 else 0
  | i, j, ℓ + 1 =>
    (if j = 0 then 0 else normalOrderCoeff i (j - 1) ℓ) +
    (↑(i + 1) * normalOrderCoeff (i + 1) j ℓ) +
    (if i = 0 then 0 else normalOrderCoeff (i - 1) j ℓ)

def bijCoeffFormula (i j ℓ : ℕ) : ℚ :=
  if i + j ≤ ℓ ∧ (ℓ - i - j) % 2 = 0 then
    (ℓ.factorial : ℚ) /
      (2 ^ ((ℓ - i - j) / 2) * i.factorial * j.factorial * ((ℓ - i - j) / 2).factorial)
  else 0

abbrev bijCoeff := normalOrderCoeff

def pairsLE (ℓ : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (ℓ + 1)) ×ˢ (Finset.range (ℓ + 1))).filter fun p => p.1 + p.2 ≤ ℓ
