/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

/-- A real sequence is a function from the natural numbers to the reals, i.e. `ℕ → ℝ`. -/
def RealSequence := ℕ → ℝ

/-- A real sequence `x` is bounded if there exists a non-negative real `B` such that
`|x n| ≤ B` for every `n : ℕ`. -/
def IsBoundedSeq (x : ℕ → ℝ) : Prop := ∃ B : ℝ, 0 ≤ B ∧ ∀ n, |x n| ≤ B
