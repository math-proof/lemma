/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/PrimalityProving.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Multiplicity
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.GroupTheory.OrderOfElement
import sympy.atlas.v1.Atlas.EllipticCurves.code.PointCounting
import Lemma.Complex.Atlas.v1.EllipticCurves.code.PointCounting

/-- `N` is a Carmichael number if it is a composite integer greater than `1`
for which every unit `a` in `ZMod N` satisfies `a ^ (N - 1) = 1`. -/
def IsCarmichael (N : ℕ) : Prop :=
  ¬N.Prime ∧ 1 < N ∧ ∀ a : ZMod N, IsUnit a → a ^ (N - 1) = 1

open scoped Nat

/-- The exponent `s` in the Miller-Rabin decomposition `N - 1 = 2^s * d`,
defined as the `2`-adic valuation of `N - 1`. -/
noncomputable def millerRabinS (N : ℕ) : ℕ := multiplicity 2 (N - 1)

/-- The odd part `d` in the Miller-Rabin decomposition `N - 1 = 2^s * d`. -/
noncomputable def millerRabinD (N : ℕ) : ℕ := (N - 1) / 2 ^ millerRabinS N

/-- An integer `a` is a Miller-Rabin witness for the compositeness of `N` if
`a` is nonzero mod `N`, `a^d ≢ 1`, and `a^(2^r · d) ≢ -1` for every
`0 ≤ r < s`, where `N - 1 = 2^s · d` with `d` odd. -/
def IsMillerRabinWitness (N a : ℕ) : Prop :=
  (a : ZMod N) ≠ 0 ∧
  (a : ZMod N) ^ millerRabinD N ≠ 1 ∧
  ∀ r : ℕ, r < millerRabinS N → (a : ZMod N) ^ (2 ^ r * millerRabinD N) ≠ -1

noncomputable section

open Classical

/-- The set of Miller-Rabin witnesses in `[1, N-1]`. -/
def millerRabinWitnessSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun a => IsMillerRabinWitness N a)

/-- The set of Miller-Rabin liars (non-witnesses) in `[1, N-1]`. -/
def millerRabinLiarSet (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N - 1)).filter (fun a => ¬ IsMillerRabinWitness N a)

/-- The `2`-adic valuation of a natural number, computed recursively by
dividing by `2` while the input is even. -/
def twoAdicVal : ℕ → ℕ
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 0 then 1 + twoAdicVal ((n + 1) / 2) else 0
termination_by n => n
decreasing_by simp_wf; omega

/-- One iteration of the Miller-Rabin primality test for a candidate `N` with
a base `a`: succeeds iff `a^d ≡ 1` or `a^(2^r · d) ≡ -1` for some `r < s`,
where `N - 1 = 2^s · d`. -/
def millerRabinStep (N a : ℕ) : Bool :=
  let nm1 := N - 1
  let s := twoAdicVal nm1
  let d := nm1 / 2 ^ s
  ((a : ZMod N) ^ d == 1) ||
  (List.range s).any fun r => ((a : ZMod N) ^ (2 ^ r * d) == -1)

/-- The full Miller-Rabin test: run `millerRabinStep` on each witness in the
list and report `true` iff every one returns `true`. -/
def millerRabinTest (N : ℕ) (witnesses : List ℕ) : Bool :=
  witnesses.all (millerRabinStep N)

/-- A projective `z`-coordinate `Pz` is zero modulo `N` if `N` divides `Pz`. -/
def IsZeroModN (Pz : ℤ) (N : ℕ) : Prop := (N : ℤ) ∣ Pz

/-- A projective `z`-coordinate `Pz` is nonzero modulo `N` if `N` does not
divide `Pz`. -/
def IsNonzeroModN (Pz : ℤ) (N : ℕ) : Prop := ¬ IsZeroModN Pz N

/-- A projective `z`-coordinate `Pz` is strongly nonzero modulo `N` if
`gcd(Pz, N) = 1`. -/
def IsStronglyNonzeroModN (Pz : ℤ) (N : ℕ) : Prop := Int.gcd Pz ↑N = 1

/-- The hypotheses of the Goldwasser-Kilian primality criterion (Theorem 11.13
of Sutherland): `N, M > 1`, `M > (N^{1/4}+1)^2`, `N` coprime to the
discriminant of `W`, the multiple `MP` is zero mod `N`, and `(M/ℓ)P` is
strongly nonzero mod `N` for every prime `ℓ ∣ M`. -/
structure GoldwasserKilianHyp (W : WeierstrassCurve ℤ) (N M : ℕ)
    (zMP : ℤ) (zMlP : ℕ → ℤ) : Prop where
  hN : N > 1
  hM : M > 1
  hMbound : (M : ℝ) > (Real.sqrt (Real.sqrt ↑N) + 1) ^ 2
  hcop : Nat.Coprime N (Int.natAbs W.Δ)
  hzero : IsZeroModN zMP N
  hstrong : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → IsStronglyNonzeroModN (zMlP ℓ) N
