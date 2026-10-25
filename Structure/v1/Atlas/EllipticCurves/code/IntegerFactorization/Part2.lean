/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part3
open Nat Real Filter Asymptotics Finset


namespace PollardPM1

open Nat Finset

/-- Configuration data for the elliptic curve method (ECM): the modulus `N`,
the smoothness bound `B`, the prime-search bound `M`, and a witness `1 < N`. -/
structure ECMConfig where
  N : ℕ
  B : ℕ
  M : ℕ
  hN : 1 < N

/-- ECM curve parameters over `ℤ`: choice of `a` and a base point `(x₀, y₀)`.
The value of `b` is computed so that `(x₀, y₀)` lies on the curve. -/
structure ECMCurveParams where
  a : ℤ
  x₀ : ℤ
  y₀ : ℤ

end PollardPM1
