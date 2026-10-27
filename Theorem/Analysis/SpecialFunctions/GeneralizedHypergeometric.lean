import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Def.Analysis.SpecialFunctions.GeneralizedHypergeometric
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

@[simp]
theorem generalizedHypergeometricCoefficient_zero (a b : Multiset K) :
    generalizedHypergeometricCoefficient a b 0 = 1 := by
  simp [generalizedHypergeometricCoefficient]

@[simp]
theorem generalizedHypergeometricCoefficient_empty (n : ℕ) :
    generalizedHypergeometricCoefficient (0 : Multiset K) 0 n = (n.factorial : K)⁻¹ := by
  simp [generalizedHypergeometricCoefficient]

theorem generalizedHypergeometricCoefficient_cons_upper (x : K) (a b : Multiset K) (n : ℕ) :
    generalizedHypergeometricCoefficient (x ::ₘ a) b n =
      (ascPochhammer K n).eval x * generalizedHypergeometricCoefficient a b n := by
  simp [generalizedHypergeometricCoefficient, mul_assoc, mul_left_comm]

theorem generalizedHypergeometricCoefficient_cons_lower (a b : Multiset K) (x : K) (n : ℕ) :
    generalizedHypergeometricCoefficient a (x ::ₘ b) n =
      generalizedHypergeometricCoefficient a b n * ((ascPochhammer K n).eval x)⁻¹ := by
  simp only [generalizedHypergeometricCoefficient, Multiset.map_cons, Multiset.prod_cons, mul_inv]
  ac_rfl

theorem generalizedHypergeometricCoefficient_cons_both_cancel
    (x : K) (a b : Multiset K) (n : ℕ)
    (hx : (ascPochhammer K n).eval x ≠ 0) :
    generalizedHypergeometricCoefficient (x ::ₘ a) (x ::ₘ b) n =
      generalizedHypergeometricCoefficient a b n := by
  rw [generalizedHypergeometricCoefficient_cons_lower,
    generalizedHypergeometricCoefficient_cons_upper]
  calc
    (ascPochhammer K n).eval x * generalizedHypergeometricCoefficient a b n *
        ((ascPochhammer K n).eval x)⁻¹ =
      generalizedHypergeometricCoefficient a b n *
        ((ascPochhammer K n).eval x * ((ascPochhammer K n).eval x)⁻¹) := by ac_rfl
    _ = generalizedHypergeometricCoefficient a b n := by simp [hx]

theorem generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower
    (a b : Multiset K) {n k : ℕ} (hk : k < n) (hmem : -(k : K) ∈ b) :
    generalizedHypergeometricCoefficient a b n = 0 := by
  have hzero : (0 : K) ∈ b.map fun x => (ascPochhammer K n).eval x :=
    Multiset.mem_map.mpr ⟨-(k : K), hmem, ascPochhammer_eval_neg_coe_nat_of_lt hk⟩
  simp [generalizedHypergeometricCoefficient, Multiset.prod_eq_zero hzero]

theorem generalizedHypergeometricCoefficient_eq_zero_of_zero_mem_lower
    (a b : Multiset K) {n : ℕ} (hn : 0 < n) (hmem : (0 : K) ∈ b) :
    generalizedHypergeometricCoefficient a b n = 0 :=
  generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_lower a b (k := 0) hn
    (by simpa using hmem)

theorem generalizedHypergeometricCoefficient_eq_zero_of_neg_coe_nat_mem_upper
    (a b : Multiset K) {n k : ℕ} (hk : k < n) (hmem : -(k : K) ∈ a) :
    generalizedHypergeometricCoefficient a b n = 0 := by
  have hzero : (0 : K) ∈ a.map fun x => (ascPochhammer K n).eval x :=
    Multiset.mem_map.mpr ⟨-(k : K), hmem, ascPochhammer_eval_neg_coe_nat_of_lt hk⟩
  simp [generalizedHypergeometricCoefficient, Multiset.prod_eq_zero hzero]

theorem generalizedHypergeometricCoefficient_two_one (a b c : K) (n : ℕ) :
    generalizedHypergeometricCoefficient ({a, b} : Multiset K) {c} n =
      ordinaryHypergeometricCoefficient a b c n := by
  simp [generalizedHypergeometricCoefficient, ordinaryHypergeometricCoefficient, mul_assoc]

end MetaMathlibExt.GeneralizedHypergeometric
