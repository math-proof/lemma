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
import Structure.v1.Atlas.EllipticCurves.code.ECM


noncomputable section

open Nat Finset

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

end
