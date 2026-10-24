/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GeneralizedStirlingNumbers.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic

namespace MetaMathlibExt

/-- Generalized Stirling numbers of the first kind, after Carlitz and Broder,
as recorded in Cereceda (arXiv:2401.13696v4, lines 132-142; Axioms 14 (2025), 746):
`[n,m]_x = ∑_{i=0}^{n-m} choose (i+m) m * stirlingFirst n (i+m) * x^i`
for `m ≤ n`, with `x` real. The definition below uses the displayed finite sum
for every `n, m`; when `m > n`, `n - m + 1 = 1` and the single ordinary term
vanishes, giving `0`. -/
noncomputable def generalizedStirlingFirst (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose (i + m) m : ℝ) * (Nat.stirlingFirst n (i + m) : ℝ) * x ^ i)

/-- Generalized Stirling numbers of the second kind, after Carlitz and Broder,
as recorded in Cereceda (arXiv:2401.13696v4, lines 132-142; Axioms 14 (2025), 746):
`{n,m}_x = ∑_{i=0}^{n-m} choose n i * stirlingSecond (n-i) m * x^i`
for `m ≤ n`, with `x` real. The definition below uses the displayed finite sum
for every `n, m`; when `m > n`, `n - m + 1 = 1` and the single ordinary term
vanishes, giving `0`. -/
noncomputable def generalizedStirlingSecond (n m : ℕ) (x : ℝ) : ℝ :=
  Finset.sum (Finset.range (n - m + 1)) (fun i =>
    (Nat.choose n i : ℝ) * (Nat.stirlingSecond (n - i) m : ℝ) * x ^ i)
end MetaMathlibExt
