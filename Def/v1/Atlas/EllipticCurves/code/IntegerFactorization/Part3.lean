/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/IntegerFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Structure.v1.Atlas.EllipticCurves.code.IntegerFactorization
open Nat Real Filter Asymptotics Finset


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

end PollardPM1
