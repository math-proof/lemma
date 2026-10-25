/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QBinomial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic
set_option maxHeartbeats 400000

variable {k : Type*} [Field k]


/-- The Gaussian (q-)binomial coefficient `qBinomial q n m`, defined by the
recursion `qBinomial q (n+1) (m+1) = q^(m+1) * qBinomial q n (m+1) + qBinomial q n m`,
with `qBinomial q n 0 = 1` and `qBinomial q 0 (m+1) = 0`. -/
def qBinomial (q : k) : ℕ → ℕ → k
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, m + 1 => q ^ (m + 1) * qBinomial q n (m + 1) + qBinomial q n m

