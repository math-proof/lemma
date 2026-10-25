/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Nat Real Filter Asymptotics Finset


noncomputable section

/-- A natural number `n` is `B`-smooth if all of its prime factors are at most `B`,
i.e. `n ∈ Nat.smoothNumbers (B + 1)`. Smoothness is the key notion underlying
subexponential factoring algorithms. -/
def IsSmooth (B : ℕ) (n : ℕ) : Prop := n ∈ Nat.smoothNumbers (B + 1)

end
