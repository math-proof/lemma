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

/-- `B`-smoothness is decidable: it reduces to deciding membership of `n` in the
finite-indexed set `Nat.smoothNumbers (B + 1)`. -/
instance (B n : ℕ) : Decidable (IsSmooth B n) :=
  inferInstanceAs (Decidable (n ∈ Nat.smoothNumbers (B + 1)))

/-- The count `Ψ(x, y)`: the number of `⌊y⌋`-smooth positive integers up to `⌊x⌋`. -/
def smoothCount (x y : ℝ) : ℕ :=
  (Nat.smoothNumbersUpTo (⌊x⌋₊) (⌊y⌋₊ + 1)).card

/-- The Canfield–Erdős–Pomerance filter on `(u, x)`: pairs going to infinity
constrained by `u < (1 - ε) · log x / log log x`. Used to state the CEP asymptotic. -/
def cepFilter (ε : ℝ) : Filter (ℝ × ℝ) :=
  (atTop ×ˢ atTop) ⊓
    Filter.principal {p : ℝ × ℝ | p.1 < (1 - ε) * Real.log p.2 / Real.log (Real.log p.2)}

/-- Canfield–Erdős–Pomerance theorem: in the range `u < (1 - ε) log x / log log x`,
`log(Ψ(x, x^{1/u}) / x) + u log u = o(u log u)`, i.e. the density of smooth
numbers is governed by Dickman's function. -/
end

/-- The factor base of bound `B`: the finset of primes `q ≤ B`. -/
def factorBase (B : ℕ) : Finset ℕ :=
  Nat.primesBelow (B + 1)

/-- The discrete logarithm of `β ∈ G` to base `g` (where `g` generates the cyclic
group of order `n`), valued in `ZMod n`. Built by transporting through the
isomorphism `G ≃ Multiplicative (ZMod n)` induced by the generator. -/
noncomputable def dlog (β : G) : ZMod n :=
  Multiplicative.toAdd ((zmodMulEquivOfGenerator hg hn).symm β)

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

/-- The factor base associated with an index-calculus configuration. -/
def IndexCalculusConfig.factorBaseSet (cfg : IndexCalculusConfig) : Finset ℕ :=
  factorBase cfg.B

/-- Size of the factor base in the configuration. -/
def IndexCalculusConfig.factorBaseSize (cfg : IndexCalculusConfig) : ℕ :=
  cfg.factorBaseSet.card

/-- Number of relations needed to solve the linear system in index calculus:
factor-base size plus one. -/
def IndexCalculusConfig.relationsNeeded (cfg : IndexCalculusConfig) : ℕ :=
  cfg.factorBaseSize + 1

/-- Validity of a recorded relation in a group `G` with generator `g` and
factor-base lift `f`: the equation `g^{exponent} · b⁻¹ = ∏ f(q)^{factorExponents q}`
holds. -/
def IndexCalculusRelation.IsValid {G : Type*} [CommGroup G]
    (R : IndexCalculusRelation B) (g b : G) (f : ℕ → G) : Prop :=
  g ^ R.exponent * b⁻¹ = ∏ q ∈ factorBase B, f q ^ R.factorExponents q

namespace PollardPM1

open Nat Finset

/-- Pollard p−1 smooth exponent: the product `∏_{ℓ ≤ B prime} ℓ^{⌈log_ℓ N⌉}`,
guaranteed to be divisible by every `B`-smooth integer up to `N`. -/
def smoothExponent (N B : ℕ) : ℕ :=
  (Nat.primesBelow (B + 1)).prod (fun ℓ => ℓ ^ Nat.clog ℓ N)

/-- Local definition of `B`-smoothness used in the Pollard p−1 analysis:
`n ≠ 0` and every prime factor is at most `B`. -/
def IsBSmooth (B n : ℕ) : Prop :=
  n ≠ 0 ∧ ∀ p ∈ n.primeFactorsList, p ≤ B

/-- The largest prime factor of `n`, taken to be `0` if `n` has no prime factors. -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  n.primeFactorsList.foldl max 0

/-- Pollard p−1 factoring step: computes `gcd(a^m - 1, N)` for the smooth
exponent `m = smoothExponent N B`. Returns a nontrivial factor of `N` if one
is found by either `gcd(a, N)` or `gcd(a^m - 1, N)`. -/
noncomputable def pollardPM1 (N B a : ℕ) : Option ℕ :=
  let d₁ := Nat.gcd a N
  if 1 < d₁ ∧ d₁ < N then some d₁
  else
    let m := smoothExponent N B
    let b := a ^ m % N
    let d₂ := Nat.gcd (b - 1) N
    if 1 < d₂ ∧ d₂ < N then some d₂
    else none

/-- One stage of Pollard p−1: raise `b` to `ℓ^e` modulo `N`. -/
def pollardStep (N ℓ e b : ℕ) : ℕ := b ^ (ℓ ^ e) % N

/-- Short Weierstrass curve over a commutative ring: `y² = x³ + a x + b`,
realized by setting `(a₁, a₂, a₃, a₄, a₆) = (0, 0, 0, a, b)`. -/
def shortWeierstrass {R : Type*} [CommRing R] (a b : R) : WeierstrassCurve R :=
  ⟨0, 0, 0, a, b⟩

/-- ECM discriminant of the short Weierstrass curve `y² = x³ + a x + b`:
`4 a³ + 27 b²`. The full `Δ` differs by a factor `-16`. -/
def ecmDiscriminant {R : Type*} [CommRing R] (a b : R) : R :=
  4 * a ^ 3 + 27 * b ^ 2

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
