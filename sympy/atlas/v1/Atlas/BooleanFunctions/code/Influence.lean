/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Influence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Field

namespace BooleanFourier

def flipCoord {n : ℕ} (x : Fin n → Bool) (i : Fin n) : Fin n → Bool :=
  Function.update x i (!x i)

noncomputable def influence {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : ℝ :=
  ((Finset.univ.filter fun x => f x ≠ f (flipCoord x i)).card : ℝ) / (2 ^ n : ℝ)

noncomputable def totalInfluence {n : ℕ} (f : (Fin n → Bool) → Bool) : ℝ :=
  ∑ i : Fin n, influence f i

def numPivotal {n : ℕ} (f : (Fin n → Bool) → Bool) (x : Fin n → Bool) : ℕ :=
  (Finset.univ.filter fun i : Fin n => f x ≠ f (flipCoord x i)).card
