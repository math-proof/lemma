/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part2
open Nat Real Filter Asymptotics Finset


/-- A single relation collected during index calculus with smoothness bound `B`:
records the exponent on the generator and the exponent vector over the factor
base (supported within `factorBase B`). -/
structure IndexCalculusRelation (B : ℕ) where
  exponent : ℤ
  factorExponents : ℕ → ℤ
  support_subset : ∀ q, factorExponents q ≠ 0 → q ∈ factorBase B

/-- Configuration parameters for index calculus modulo a prime `p`: the prime
`p`, its primality witness, the smoothness bound `B`, and the group order
`N = p - 1`. -/
structure IndexCalculusConfig where
  p : ℕ
  hp : Nat.Prime p
  B : ℕ
  N : ℕ := p - 1

