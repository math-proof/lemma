/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Sequences/Subsequences.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace Sequences

/-- `y` is a subsequence of `x` if there is a strictly increasing index function
`φ : ℕ → ℕ` such that `y = x ∘ φ` (i.e. `y k = x (φ k)`). -/
def IsSubsequence (x y : ℕ → ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ y = x ∘ φ
