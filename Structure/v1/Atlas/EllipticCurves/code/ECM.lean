/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part4
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IntegerFactorization
import Def.v1.Atlas.EllipticCurves.code.ECM


noncomputable section

open Nat Finset

/-- Configuration data for ECM (Algorithm 10.11): the integer `N` to be factored
(with `1 < N`), a smoothness bound `B` for primes used in the scalar, and a prime bound `M`. -/
structure ECMConfig where
  N : ℕ
  B : ℕ
  M : ℕ
  hN : 1 < N

/-- The randomly chosen curve parameters used by ECM: a coefficient `a` together
with the initial point `(x₀, y₀)` on the resulting short Weierstrass curve. -/
structure ECMCurveParams where
  a : ℤ
  x₀ : ℤ
  y₀ : ℤ

end
