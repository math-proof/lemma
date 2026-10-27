import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Def.Analysis.SpecialFunctions.BasicHypergeometric
/-!
# Basic hypergeometric series `{}_r φ_s`

This file defines the coefficient

  `(a₁;q)ₙ ⋯ (aᵣ;q)ₙ / ((q;q)ₙ (b₁;q)ₙ ⋯ (bₛ;q)ₙ) * ((-1)ⁿ q^{n choose 2})^{1+s-r}`

of the general basic hypergeometric series `{}_rφ_s(a₁,…,aᵣ; b₁,…,bₛ; q, z)`
and packages the coefficients as a formal power series over `ℂ`.

Finite `q`-Pochhammer symbols are expanded as finite products:

* `(a;q)ₙ = ∏_{j=0}^{n-1} (1 - a q^j)`,
* `(q;q)ₙ = ∏_{j=0}^{n-1} (1 - q^{j+1})`.

The normalization exponent `1 + s - r` is computed in `ℤ`, so the definition also covers the
cases where this exponent is negative (when `r > s+1`), where the integer power is Mathlib's
totalized `zpow` on `ℂ`.

The definitions are formal and algebraic. Division and integer powers use Mathlib's totalized
operations on `ℂ`; analytic applications must separately establish that the denominator does not
vanish (in particular `b_j ∉ {q^{-k} : k ∈ ℕ}` and `q` not a root of unity) and convergence
conditions. No nonvanishing or convergence hypothesis is imposed here, so zero-denominator cases
are covered as totalized values.

## Main definitions

* `MetaMathlibExt.BasicHypergeometric.basicHypergeometricCoefficient`
* `MetaMathlibExt.BasicHypergeometric.basicHypergeometricSeries`

## Main results

* `basicHypergeometricCoefficient_zero`
* `coeff_basicHypergeometricSeries`
* `basicHypergeometricCoefficient_phi_succ`

## References

* [NIST Digital Library of Mathematical Functions, §17.4][dlmf17.4]

[dlmf17.4]: https://dlmf.nist.gov/17.4
-/


namespace MetaMathlibExt.BasicHypergeometric

open Finset

@[simp]
theorem basicHypergeometricCoefficient_zero {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) : basicHypergeometricCoefficient a b q 0 = 1 := by
  simp [basicHypergeometricCoefficient]

@[simp]
theorem coeff_basicHypergeometricSeries {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) (n : ℕ) :
    PowerSeries.coeff n (basicHypergeometricSeries a b q) =
      basicHypergeometricCoefficient a b q n := by
  simp [basicHypergeometricSeries]

/-- For a `{}_{s+1}φ_s` series the normalization exponent `1 + s - (s+1)` is `0` and the
normalization factor `((-1)^n q^{n choose 2})^{1+s-r}` disappears. -/
theorem basicHypergeometricCoefficient_phi_succ (s : ℕ) (a : Fin (s + 1) → ℂ)
    (b : Fin s → ℂ) (q : ℂ) (n : ℕ) :
    basicHypergeometricCoefficient a b q n =
      (∏ i, ∏ j ∈ range n, (1 - a i * q ^ j)) /
        ((∏ j ∈ range n, (1 - q ^ (j + 1))) * ∏ i, ∏ j ∈ range n, (1 - b i * q ^ j)) := by
  simp [basicHypergeometricCoefficient, Nat.cast_add, add_comm]

end MetaMathlibExt.BasicHypergeometric
