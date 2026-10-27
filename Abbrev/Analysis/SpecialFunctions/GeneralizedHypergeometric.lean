import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Def.Analysis.SpecialFunctions.GeneralizedHypergeometric.Part3
/-!
# Generalized hypergeometric series `ₚF_q`

This file defines the ordinary generalized hypergeometric coefficient

  `pFqCoeff(a, b, n) = (a₁)ₙ ⋯ (aₚ)ₙ / ((b₁)ₙ ⋯ (b_q)ₙ · n!)`

over an arbitrary field `K` and packages it as a `FormalMultilinearSeries`.
Here `(x)ₙ = (ascPochhammer K n).eval x` is the ascending Pochhammer symbol
`x·(x+1)⋯(x+n-1)` with `(x)₀ = 1`, and `p = a.card`, `q = b.card`.

Parameters are `Multiset K` because only multiplicity matters and order is
irrelevant; this matches Mathlib's `Complex.regularizedHGFunCoeff` API and
retains repeated parameters, while removing the source archive's ordered `List`
and permutation wrappers.

The definition uses totalized inverses in `K`.  A vanishing lower Pochhammer
product or factorial cast therefore gives the totalized value `0` rather than an
undefined term.  In particular the coefficient is defined as a formal algebraic
expression even at singular lower parameters `bᵢ ∈ {0, -1, -2, …}` and in
positive characteristic where `(n ! : K) = 0`; no analytic convergence claim is
made.  The regularized variant `Complex.regularizedHGFunCoeff` is distinct: it
is `ℂ`-only and replaces `((bᵢ)ₙ)⁻¹` by `(Γ(bᵢ+n))⁻¹`.

## Main definitions

* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricCoefficient`
* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricSeries`

## Main results

* Construction: `generalizedHypergeometricCoefficient_zero`,
  `generalizedHypergeometricCoefficient_empty`,
  `generalizedHypergeometricCoefficient_cons_upper`,
  `generalizedHypergeometricCoefficient_cons_lower`
* Cancellation of a common non-singular parameter:
  `generalizedHypergeometricCoefficient_cons_both_cancel`
* Singular lower boundary (totalized `0`):
  `generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower`,
  `generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower`
* Singular upper boundary:
  `generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper`
* Compatibility with Mathlib's `₂F₁`:
  `generalizedHypergeometricCoefficient_two_one`,
  `generalizedHypergeometricSeries_two_one`
* Formal series packaging:
  `generalizedHypergeometricSeries_apply_eq`,
  `generalizedHypergeometricSeries_apply_zero`

## Analytic layer (ℂ)

Following arXiv:2608.10675 `KMY-Conj.tex:456-470`, `_{m+1}F_m` is presented as
the infinite sum of Pochhammer-product coefficients with lower parameters
excluded from `ℤ_{\le 0}`. The `ℂ`-valued `tsum` is defined unconditionally
as `∑' n, coeff n * z^n`; admissibility and summability appear only as
hypotheses of theorems where they are used. The source asserts absolute
convergence for `|z| < 1`, but this module proves only the terminating
finite-support case, not a radius theorem. The finite-sum identification
for a terminating upper parameter `-(N:ℂ)` is a generic algebraic consequence
of `ascPochhammer_eval_neg_coe_nat_of_lt` and needs no admissibility.

## Analytic definitions

* `MetaMathlibExt.GeneralizedHypergeometric.LowerParametersAdmissible`
* `MetaMathlibExt.GeneralizedHypergeometric.SummableHypergeometric`
* `MetaMathlibExt.GeneralizedHypergeometric.generalizedHypergeometricValue`

## Analytic statements

* `generalizedHypergeometricValue_eq_tsum`, `generalizedHypergeometricValue_hasSum`
* `lowerParametersAdmissible_ascPochhammer_ne_zero`,
  `lowerParametersAdmissible_forall_mem_ne_zero`
* `summableHypergeometric_of_neg_coe_nat_mem_upper`
* `generalizedHypergeometric_tsum_eq_finset_sum`,
  `generalizedHypergeometricValue_terminating_eq_finset_sum`

## References

* [Evaluations of the areal Mahler measure of multivariable
  polynomials](https://arxiv.org/abs/2306.15727)
* [Two supercongruences involving truncated hypergeometric
  series](https://arxiv.org/abs/2307.10000)
* [A proof of a weighted sum conjecture for finite multiple zeta values of level
  two](https://arxiv.org/abs/2608.10675)
-/


namespace MetaMathlibExt.GeneralizedHypergeometric

variable {K : Type*} [Field K]

variable {A : Type*} [Ring A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]

/-- Convergence predicate: the coefficient-weighted power series is `Summable`.
The source asserts absolute convergence for `|z| < 1` without proof;
this predicate exposes `Summable` without claiming a radius theorem. -/
abbrev SummableHypergeometric (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => generalizedHypergeometricCoefficient a b n * z ^ n)

end MetaMathlibExt.GeneralizedHypergeometric
