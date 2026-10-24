/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/RussoMargulis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Monotone
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Monotone

namespace BooleanFourier

open Finset BigOperators

def flipBit {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

noncomputable def pBiasedWeight (n : ℕ) (p : ℝ) (x : Fin n → Bool) : ℝ :=
  ∏ i : Fin n, if x i then p else (1 - p)

noncomputable def pBiasedExpectation {n : ℕ} (f : (Fin n → Bool) → Bool) (p : ℝ) : ℝ :=
  ∑ x : Fin n → Bool, pBiasedWeight n p x * if f x then 1 else 0

noncomputable def pBiasedInfluence {n : ℕ} (f : (Fin n → Bool) → Bool)
    (i : Fin n) (p : ℝ) : ℝ :=
  ∑ x : Fin n → Bool, pBiasedWeight n p x *
    if f x ≠ f (flipBit x i) then 1 else 0
