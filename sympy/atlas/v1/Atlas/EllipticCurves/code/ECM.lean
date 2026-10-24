/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ECM.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import sympy.atlas.v1.Atlas.EllipticCurves.code.IntegerFactorization
import Lemma.Complex.Atlas.v1.EllipticCurves.code.IntegerFactorization

noncomputable section

open Nat Finset

/-- The short Weierstrass curve `y² = x³ + a x + b` over a commutative ring `R`,
represented as a `WeierstrassCurve` with `a₁ = a₂ = a₃ = 0`, `a₄ = a` and `a₆ = b`. -/
def shortWeierstrass {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a, b⟩

/-- The discriminant quantity `4 a³ + 27 b²` of the short Weierstrass curve
`y² = x³ + a x + b`, used by ECM (Algorithm 10.11) to detect a nontrivial gcd with `N`. -/
def ecmDiscriminant {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 + 27 * b ^ 2

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

/-- The coefficient `b = y₀² - x₀³ - a x₀` derived from `(a, x₀, y₀)` so that the
short Weierstrass curve `y² = x³ + a x + b` passes through `(x₀, y₀)`. -/
def ECMCurveParams.b (params : ECMCurveParams) : ℤ :=
  params.y₀ ^ 2 - params.x₀ ^ 3 - params.a * params.x₀

/-- The short Weierstrass curve over `ℤ` determined by `params`. -/
def ECMCurveParams.curve (params : ECMCurveParams) : WeierstrassCurve ℤ :=
  shortWeierstrass params.a params.b

/-- The discriminant `4 a³ + 27 b²` of the ECM curve defined by `params`. -/
def ECMCurveParams.disc (params : ECMCurveParams) : ℤ :=
  ecmDiscriminant params.a params.b

/-- Reduce the ECM curve modulo a prime `p`, viewing it as an affine curve over `ZMod p`. -/
def ECMCurveParams.curveModP (params : ECMCurveParams) (p : ℕ) :
    WeierstrassCurve.Affine (ZMod p) :=
  params.curve.map (Int.castRingHom (ZMod p))

/-- The exponent `e` such that `ℓ^{e-1} ≤ (√M + 1)² < ℓ^e`, as used by ECM
to ensure every smooth order ≤ `(√M + 1)²` divides the scaled scalar. -/
def ecmSmoothExponent (ℓ M : ℕ) : ℕ :=
  Nat.log ℓ ((Nat.sqrt M + 1) ^ 2) + 1

/-- The ECM scalar multiplier: the product `∏_{ℓ < B prime} ℓ^{ecmSmoothExponent ℓ M}`,
designed so that every `B`-smooth integer ≤ `(√M + 1)²` divides it. -/
def ecmSmoothScalar (B M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range B).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- Partial ECM scalar accumulated up to and including the prime `ℓ₁`: the product
`∏_{ℓ ≤ ℓ₁ prime} ℓ^{ecmSmoothExponent ℓ M}`. -/
def ecmPartialScalar (ℓ₁ M : ℕ) : ℕ :=
  ∏ ℓ ∈ (Finset.range (ℓ₁ + 1)).filter Nat.Prime, ℓ ^ ecmSmoothExponent ℓ M

/-- The outcome of one trial of ECM (Algorithm 10.11): either a proper nontrivial
divisor `d` of `N` (with `1 < d < N`, `d ∣ N`), or `failure`. -/
inductive ECMResult (N : ℕ) where
  | factor (d : ℕ) (hd_gt : 1 < d) (hd_lt : d < N) (hd_dvd : d ∣ N) : ECMResult N
  | failure : ECMResult N

/-- `ECMResult.isSuccess` is `True` exactly when the result is a factor, `False` on failure. -/
def ECMResult.isSuccess {N : ℕ} : ECMResult N → Prop
  | ECMResult.factor _ _ _ _ => True
  | ECMResult.failure => False
