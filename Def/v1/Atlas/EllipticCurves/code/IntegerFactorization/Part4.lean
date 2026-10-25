/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.IntegerFactorization.Part2
open Nat Real Filter Asymptotics Finset


namespace PollardPM1

open Nat Finset

/-- The constant term `b` of the ECM curve, chosen so that `(x₀, y₀)` lies on
`y² = x³ + a x + b`. -/
def ECMCurveParams.b (params : ECMCurveParams) : ℤ :=
  params.y₀ ^ 2 - params.x₀ ^ 3 - params.a * params.x₀

/-- The elliptic curve over `ℤ` associated to ECM parameters. -/
def ECMCurveParams.curve (params : ECMCurveParams) : WeierstrassCurve ℤ :=
  shortWeierstrass params.a params.b

/-- ECM discriminant of the chosen curve. -/
def ECMCurveParams.disc (params : ECMCurveParams) : ℤ :=
  ecmDiscriminant params.a params.b

/-- The ECM curve reduced modulo a prime `p`, viewed as an affine
Weierstrass curve over `ZMod p`. -/
def ECMCurveParams.curveModP (params : ECMCurveParams) (p : ℕ) :
    WeierstrassCurve.Affine (ZMod p) :=
  params.curve.map (Int.castRingHom (ZMod p))

/-- Per-prime exponent used in ECM: `⌊log_ℓ ((√M + 1)²)⌋ + 1`, large enough
to cover any prime-power up to `(√M + 1)²` as a factor of the multiplier. -/
def ecmSmoothExponent (ℓ M : ℕ) : ℕ :=
  Nat.log ℓ ((Nat.sqrt M + 1) ^ 2) + 1

/-- ECM smooth scalar `k = ∏_{ℓ < B prime} ℓ^{ecmSmoothExponent ℓ M}`: every
`B`-smooth integer at most `(√M + 1)²` divides this scalar. -/
def ecmSmoothScalar (B M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range B).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- The Montgomery form equation `B y² = x³ + A x² + x` over a field `k`. -/
def MontgomeryOnCurve (A B x y : k) : Prop :=
  B * y ^ 2 = x ^ 3 + A * x ^ 2 + x

/-- A point `(x, 0)` of order 2 on the Montgomery curve `B y² = x³ + A x² + x`,
characterized by lying on the curve with `y = 0` and `x ≠ 0`. -/
def IsOrder2Point (A B x : k) : Prop :=
  MontgomeryOnCurve A B x 0 ∧ x ≠ 0

/-- A point `(x, y)` of order 4 on the Montgomery curve: a curve point with
`y ≠ 0` and `x = ±1`. -/
def IsOrder4Point (A B x y : k) : Prop :=
  MontgomeryOnCurve A B x y ∧ y ≠ 0 ∧ (x = 1 ∨ x = -1)

/-- The Montgomery curve has an order-4 rational subgroup if it has either
two distinct order-2 points or an order-4 point. -/
def HasSubgroupOfOrder4 (A B : k) : Prop :=
  (∃ x₁ x₂ : k, x₁ ≠ x₂ ∧ IsOrder2Point A B x₁ ∧ IsOrder2Point A B x₂) ∨
  (∃ x y : k, IsOrder4Point A B x y)

/-- The short Weierstrass equation `y² = x³ + a x + b` over `k`. -/
def ShortWeierstrassOnCurve (a b x y : k) : Prop :=
  y ^ 2 = x ^ 3 + a * x + b

end PollardPM1
