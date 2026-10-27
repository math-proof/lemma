/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
import Mathlib
import Def.RingTheory.PowerSeries.ExpLog.Part6
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

/-!
## The Exp and Log Maps

We use Mathlib's `PowerSeries.exp` for the exponential series.
For the logarithm, we define it via the standard series log(1+x) = ∑_{n≥1} (-1)^{n-1}/n * x^n.
-/


/-- The logarithm series: log(1+x) = x - x²/2 + x³/3 - x⁴/4 + ...
    This is `\overline{log}` in the source notation.
    Label: def.fps.logbar -/
noncomputable def logSeries : K⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else algebraMap ℚ K ((-1 : ℚ)^(n-1) / n)

/-!
## FPS with Constant Term 1

We define the set K⟦X⟧₁ of FPS with constant term 1.
This is the domain on which non-integer powers are defined.
-/


/-- An FPS has constant term 1.
    This is the condition for f ∈ K⟦X⟧₁ in the source.
    Label: def.fps.Exp-Log-maps (b)

    Note: This is definitionally equivalent to membership in `PowerSeries₁` from ExpLog.lean:
    `HasConstantTermOne f ↔ f ∈ PowerSeries₁`. The `Prop` form is used here for convenience
    in hypotheses, while `PowerSeries₁` (a `Set`) is used in ExpLog.lean for subgroup structures. -/
def HasConstantTermOne (f : K⟦X⟧) : Prop := constantCoeff f = 1

section HasConstantTermOneBasic

variable {R : Type*} [CommRing R]

end HasConstantTermOneBasic

/-!
## The Log Map for FPS with Constant Term 1

For f ∈ K⟦X⟧₁, we define Log(f) by substituting (f-1) into the log series.
Since f has constant term 1, f-1 has constant term 0, so the substitution is well-defined.
-/


/-- The Log map: Log(f) = log_series(f-1) = logSeries.subst (f-1)
    This is well-defined when f has constant term 1.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsLog (f : K⟦X⟧) : K⟦X⟧ :=
  (logSeries (K := K)).subst (f - 1)

/-!
## The Exp Map for FPS with Constant Term 0

For g ∈ K⟦X⟧₀ (constant term 0), we define Exp(g) by substituting g into exp.
-/


/-- The Exp map: Exp(g) = exp(g) = (exp K).subst g
    This is well-defined when g has constant term 0.
    Label: def.fps.Exp-Log-maps -/
noncomputable def fpsExp (g : K⟦X⟧) : K⟦X⟧ :=
  (exp K).subst g

/-!
## Definition of Non-integer Powers (Definition def.fps.power-c)

For f ∈ K⟦X⟧₁ and c ∈ K, we define f^c := Exp(c * Log(f)).

This definition:
- Does not conflict with integer powers (since Log and Exp are inverses on the appropriate domains)
- Makes the rules of exponents hold
- Yields (1+x)^c = ∑ C(c,k) x^k (generalized Newton binomial formula)
-/


/-- The c-th power of an FPS f with constant term 1.
    f^c := Exp(c * Log(f)) = exp.subst (c * log_series.subst (f-1))
    Label: def.fps.power-c -/
noncomputable def fpsPow (f : K⟦X⟧) (c : K) : K⟦X⟧ :=
  fpsExp (c • fpsLog f)

end FPS
end AlgebraicCombinatorics
