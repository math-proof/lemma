/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LSeries/AbelContinuation.lean -/

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
open Filter Asymptotics MeasureTheory Topology Set Complex

/-!
# Abel continuation of Dirichlet series under partial-sum bounds

For `f : ℕ → ℂ`, let `A(n) = ∑ k ∈ Finset.Icc 1 n, f k` be the one-based
partial sums. Under a genuine `IsBigO atTop` bound `A(n) = O(n ^ σ)` for an
arbitrary real `σ`, the Abel integral

  `F_f(s) = s * ∫ x in Set.Ioi (1 : ℝ), A(⌊x⌋₊) * x ^ (-s - 1) dx`

(using exact Mathlib conventions, as in `LSeries_eq_mul_integral`) converges
for `σ < s.re`, is complex differentiable there, hence analytic on the
half-plane. The ordered Dirichlet partial sums
`∑ n ∈ Finset.Icc 1 N, LSeries.term f s n` converge to `F_f(s)` under the
same hypotheses alone (no summability): this is genuine conditional
convergence, proved by Abel summation. Only the agreement
`F_f(s) = LSeries f s` needs `LSeriesSummable f s` (and `0 ≤ σ`, which the
`LSeries_eq_mul_integral` API requires). We prove nothing about
`LSeries f` itself where it is nonsummable: its `tsum`-based definition
collapses to `0` there.

## Main definitions

* `abelPartialSum f n`: the one-based partial sums `∑ k ∈ Finset.Icc 1 n, f k`.
* `abelSummatory f`: the step function `t ↦ abelPartialSum f ⌊t⌋₊` on `ℝ`.
* `abelContinuation f s`: the Abel continuation `F_f(s)` above.

## Main results

* `differentiableAt_abelContinuation`: pointwise complex differentiability on
  `σ < s.re` for arbitrary real `σ`, via the Mellin transform identity
  `F_f(s) = s * mellin (abelSummatory f) (-s)` and
  `mellin_differentiableAt_of_isBigO_rpow`.
* `analyticOn_abelContinuation`: set-level analyticity on the half-plane,
  for arbitrary real `σ`.
* `tendsto_abelContinuation_Icc`: convergence of ordered Dirichlet partial
  sums to `F_f(s)` from the growth hypothesis and `σ < s.re` alone, via
  public `tendsto_sum_mul_atTop_nhds_one_sub_integral₀`.
* `abelContinuation_eq_LSeries`: agreement with `LSeries f s` under
  `LSeriesSummable f s` (requires `0 ≤ σ`, inherited from Mathlib's
  `LSeries_eq_mul_integral`).
-/


noncomputable section

/-- One-based partial sums of `f`. -/
def abelPartialSum (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 1 n, f k

/-- The summatory step function `t ↦ A(⌊t⌋₊)` on `ℝ`. -/
def abelSummatory (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  abelPartialSum f ⌊t⌋₊

/-- The Abel continuation `F_f(s) = s * ∫ x in Ioi 1, A(⌊x⌋) * x^(-s-1)`,
in the exact conventions of `LSeries_eq_mul_integral`. -/
def abelContinuation (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  s * ∫ t : ℝ in Set.Ioi (1 : ℝ), abelSummatory f t * (t : ℂ) ^ (-(s + 1))

end
