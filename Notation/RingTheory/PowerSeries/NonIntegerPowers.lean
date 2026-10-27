/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.ExpLog.Part6
import Def.RingTheory.PowerSeries.NonIntegerPowers
open scoped Polynomial PowerSeries
open PowerSeries Finset

/-!
# Non-integer Powers of Formal Power Series

This file formalizes non-integer powers of formal power series (FPS) and the generalized
Newton binomial formula, following Section 7.12 (sec.gf.nips) of the source.

## Main Definitions

* `AlgebraicCombinatorics.FPS.fpsPow`: The c-th power f^c for f ∈ K⟦X⟧₁ (FPS with constant term 1) and c ∈ K,
  defined as `Exp(c * Log f)` (Definition def.fps.power-c).

## Main Results

* `AlgebraicCombinatorics.FPS.fpsPow_add`: The rule f^{a+b} = f^a * f^b (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_mul`: The rule (fg)^a = f^a * g^a (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.fpsPow_pow`: The rule (f^a)^b = f^{ab} (Theorem thm.fps.power-c.rules).
* `AlgebraicCombinatorics.FPS.generalizedNewtonBinomial`: The generalized Newton binomial formula
  (1+x)^c = ∑_{k ∈ ℕ} C(c,k) x^k (Theorem thm.fps.gen-newton).
* `AlgebraicCombinatorics.FPS.binomialIdentity`: The binomial identity
  ∑_{i=0}^k C(n+i-1,i) C(n,k-2i) = C(n+k-1,k) (Proposition prop.binom.nCk-2i-qedmo.CN).

## Implementation Notes

The definition of f^c uses the Exp and Log maps from Mathlib. Specifically:
- For f ∈ K⟦X⟧₁ (constant term 1), we define f^c := Exp(c * Log f)
- This requires K to be a commutative ℚ-algebra

The generalized Newton binomial formula is proved using the polynomial identity trick:
both sides are polynomials in c that agree on ℕ, hence they agree everywhere.

## References

* Source: NonIntegerPowers.tex, Section sec.gf.nips
-/


namespace AlgebraicCombinatorics

namespace FPS

variable {K : Type*} [CommRing K] [Algebra ℚ K]

/-- Notation for non-integer powers (when needed) -/
scoped notation:80 f " ^ᶠ " c:81 => fpsPow f c

end FPS
end AlgebraicCombinatorics
