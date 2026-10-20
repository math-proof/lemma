/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianGenocchiFormula.lean -/

import sympy.atlas.NumberTheory.GenocchiNumber
import Mathlib.Combinatorics.Enumerative.Stirling
import sympy.atlas.Combinatorics.Enumerative.GarabedianBernoulliStirling
import sympy.atlas.NumberTheory.GenocchiBernoulli
open scoped BigOperators

namespace MetaMathlibExt

section

/-- Garabedian's explicit formula for the Genocchi numbers, for every `n : ℕ`:
`G n = n * ∑ k = 1..n, (-1)^(n-k) * (k-1)! * S(n, k) / 2^(k-1)`. At `n = 0` both sides are `0`.
`genocchiNumber_eq_stirlingSecond_sum` is the source-shaped form. -/
theorem genocchiNumber_eq_stirlingSecond_sum_general (n : ℕ) :
    genocchiNumber n =
      (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
          (2 : ℚ) ^ (k - 1) :=
  (genocchiNumber_eq_bernoulli n).trans (garabedian_genocchi_formula_general n)

set_option linter.unusedVariables false in
/-- Garabedian's explicit formula for the Genocchi numbers: for `n ≥ 1`,
`G n = n * ∑ k = 1..n, (-1)^(n-k) * (k-1)! * S(n, k) / 2^(k-1)`,
where the left-hand side uses the canonical generating-function definition
`genocchiNumber`; the source identifies that same sequence with its Bernoulli
formula, exactly the first equality in the source's displayed formula (g19).

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note on Explicit Formulas
for Bernoulli and Genocchi Numbers," Journal of Integer Sequences 28 (2025),
Article 25.6.7, lines 184–194 of the official TeX:
<https://cs.uwaterloo.ca/journals/JIS/VOL28/Zerroukhat/zerrou3.tex>.

Historical attribution: H. L. Garabedian, "A new formula for the Bernoulli
numbers," Bulletin of the American Mathematical Society 46 (1940), 531–533,
DOI `10.1090/S0002-9904-1940-07255-6`.

Since `k ∈ Finset.Icc 1 n`, both natural subtractions `n - k` and `k - 1`
are genuine differences. It follows from `genocchiNumber_eq_stirlingSecond_sum_general`; the
hypothesis `hn` is unused and keeps the source's shape.

Proves `Wanted` entry `genocchiNumber_eq_stirlingSecond_sum`.
-/
@[nolint unusedArguments]
theorem genocchiNumber_eq_stirlingSecond_sum (n : ℕ)
    (hn : 1 ≤ n) :
    genocchiNumber n =
      (n : ℚ) * ∑ k ∈ Finset.Icc 1 n,
        (-1 : ℚ) ^ (n - k) * (Nat.factorial (k - 1) : ℚ) * (Nat.stirlingSecond n k : ℚ) /
          (2 : ℚ) ^ (k - 1) :=
  genocchiNumber_eq_stirlingSecond_sum_general n

end

end MetaMathlibExt
