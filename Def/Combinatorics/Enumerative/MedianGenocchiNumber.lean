/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MedianGenocchiNumber.lean -/

import Mathlib.NumberTheory.Bernoulli
open scoped BigOperators

/-!
# Median Genocchi numbers

The definitions follow Kwang-Wu Chen, *An Interesting Lemma for Regular
C-fractions*, Journal of Integer Sequences 13 (2010), Article 10.5.3.
-/


namespace MetaMathlibExt

/-- The Genocchi numbers, represented by the Bernoulli-number formula
`G n = 2 * (1 - 2^n) * B n`. -/
def genocchiNumberViaBernoulli (n : ℕ) : ℚ :=
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n

/-- The odd-indexed median Genocchi value `H_(2n+1)`.

For `n > 0`, this is the source's finite sum
`sum k = 0..floor((n-1)/2), choose n (2k+1) * G_(2n-2k)`.
Stable source identifiers: concept `jis_sem_7cda4ff413e183d46cd0c8e9`;
statements `jis_94b979a01da48153660bbf5f` and
`jis_41a43df0c7633bde6c183242`.
-/
def medianGenocchiOdd (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ∑ k ∈ Finset.range ((n - 1) / 2 + 1),
    (Nat.choose n (2 * k + 1) : ℚ) * genocchiNumberViaBernoulli (2 * n - 2 * k)

end MetaMathlibExt
