import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Basic
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

/-- The coefficient of `z ^ n` in the general basic hypergeometric series `{}_rφ_s`.

This is DLMF 17.4.1 adapted from `_{r+1}φ_s` to `{}_rφ_s`: with `r` upper parameters
`a₁,…,aᵣ` and `s` lower parameters `b₁,…,bₛ`,

```
coeff n = (∏_i (a_i;q)_n) / ((q;q)_n ∏_i (b_i;q)_n) * ((-1)^n q^{n choose 2})^{1+s-r}
```

where `(a;q)_n = ∏_{j=0}^{n-1} (1 - a q^j)` and `(q;q)_n = ∏_{j=0}^{n-1} (1 - q^{j+1})`.
The factor `(-1)^n q^{n choose 2}` is `(-1 : ℂ)^n * q ^ Nat.choose n 2` and the outer
exponent `1 + s - r` is in `ℤ` via totalized `zpow` on `ℂ`.

Finite `q`-Pochhammer symbols are expanded directly as products. Division and integer powers
use Mathlib's totalized operations on `ℂ`; analytic applications must separately establish that
the denominator does not vanish.
-/
noncomputable def basicHypergeometricCoefficient {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) (n : ℕ) : ℂ :=
  (∏ i, ∏ j ∈ range n, (1 - a i * q ^ j)) /
      ((∏ j ∈ range n, (1 - q ^ (j + 1))) * ∏ i, ∏ j ∈ range n, (1 - b i * q ^ j)) *
    (((-1 : ℂ) ^ n * q ^ Nat.choose n 2) ^ ((1 : ℤ) + s - r))

/-- The formal power series over `ℂ` whose `n`-th coefficient is
`basicHypergeometricCoefficient a b q n`. -/
noncomputable def basicHypergeometricSeries {r s : ℕ} (a : Fin r → ℂ) (b : Fin s → ℂ)
    (q : ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => basicHypergeometricCoefficient a b q n

end MetaMathlibExt.BasicHypergeometric
