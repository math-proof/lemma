/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/QBinomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.YoungDiagrams
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungDiagrams
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin

set_option autoImplicit false

open Polynomial

namespace QBinomial

noncomputable def qBinom : ℕ → ℕ → Polynomial ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | k + 1, j + 1 =>
    if j + 1 > k + 1 then 0
    else qBinom k (j + 1) + (X : Polynomial ℤ) ^ (k - j) * qBinom k j

@[simp] theorem qBinom_zero_zero : qBinom 0 0 = 1 := rfl
@[simp] theorem qBinom_zero_succ (j : ℕ) : qBinom 0 (j + 1) = 0 := rfl
@[simp] theorem qBinom_succ_zero (k : ℕ) : qBinom (k + 1) 0 = 1 := rfl

@[simp] theorem qBinom_zero_right (k : ℕ) : qBinom k 0 = 1 := by
  cases k <;> simp

noncomputable def rankGenPoly (m n : ℕ) : Polynomial ℤ :=
  ∑ p : Lmn m n, (X : Polynomial ℤ) ^ sumParts p
