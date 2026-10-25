/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/PrimeLog.lean -/

import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.LSeries.Nonvanishing
open scoped LSeries.notation

/-!
# Meromorphic continuation of the prime logarithmic Dirichlet series

This module formalizes NumberTheoryI Lemma 16.11: for the prime logarithmic
series `Φ(s) = ∑_p log p / p ^ s`, the difference `Φ(s) - 1 / (s - 1)` admits a
single meromorphic continuation to `Re s > 1 / 2` which is holomorphic on the
closed half-plane `Re s ≥ 1`.

The proof follows the classical route.  Writing the von Mangoldt L-series over
prime powers splits off the prime terms from the higher prime powers:
`L(Λ, s) = Φ(s) + C(s)` on `Re s > 1`, where the correction series `C(s)`
already converges for `Re s > 1 / 2`.  Since `L(Λ, s) = -ζ'(s) / ζ(s)` and
`ζ(s) = (s - 1)⁻¹ * ζ₁(s)` with `ζ₁` entire and nonvanishing on `Re s ≥ 1`,
the canonical continuation is `-ζ₁'(s) / ζ₁(s) - C(s)`.

## Main definitions

* `Nat.Primes.logDirichletSeries`: the prime sum `Φ(s)`.
* `Nat.Primes.logDirichletCorrectionTerm`: one higher-prime-power summand.
* `Nat.Primes.logDirichletCorrection`: the correction series `C(s)`.
* `Nat.Primes.logDirichletContinuation`: the canonical continuation.

## Main results

* `Nat.Primes.logDirichletCorrection_analyticOn`: `C` is analytic on `Re > 1/2`.
* `Nat.Primes.logDirichlet_vonMangoldt_split`: `L(Λ, s) = Φ(s) + C(s)`.
* `Nat.Primes.logDirichletSeries_eq`: `Φ` via the zeta logarithmic derivative.
* `Nat.Primes.logDirichletContinuation_meromorphic`: meromorphicity on `Re > 1/2`.
* `Nat.Primes.logDirichletContinuation_analyticOn`: analyticity on `Re ≥ 1`.
* `Nat.Primes.logDirichletContinuation_agree`: agreement with `Φ - 1/(·-1)`.
* `Nat.Primes.logDirichlet_meromorphicContinuation`: the combined endpoint.
-/


namespace Nat.Primes

/-- The prime logarithmic Dirichlet series `Φ(s) = ∑_p log p / p ^ s`. -/
noncomputable def logDirichletSeries (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, (Real.log ((p : ℕ) : ℝ) : ℂ) / (((p : ℕ)) : ℂ) ^ s

/-- One summand of the higher-prime-power correction series. -/
noncomputable def logDirichletCorrectionTerm (p : Nat.Primes) (k : ℕ) (s : ℂ) : ℂ :=
  (Real.log ((p : ℕ) : ℝ) : ℂ) / (Nat.cast ((p : ℕ) ^ (k + 2)) : ℂ) ^ s

/-- The higher-prime-power correction series `C(s) = ∑_{p, k} log p / p ^ ((k+2) s)`. -/
noncomputable def logDirichletCorrection (s : ℂ) : ℂ :=
  ∑' x : Nat.Primes × ℕ, logDirichletCorrectionTerm x.1 x.2 s

/-- The canonical continuation of `Φ(s) - 1 / (s - 1)` to `Re s > 1 / 2`. -/
noncomputable def logDirichletContinuation (s : ℂ) : ℂ :=
  -(deriv riemannZeta₁ s / riemannZeta₁ s) - logDirichletCorrection s

end Nat.Primes
