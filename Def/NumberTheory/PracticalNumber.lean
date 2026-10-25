/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PracticalNumber.lean -/

import Mathlib.NumberTheory.Divisors


namespace MetaMathlibExt

open scoped BigOperators

/-- Practical number predicate (concept `jis_term_8ed6008fc4e01e1cc05ff7f6`, source
lines 94–98): a positive `n` such that every positive `m ≤ n` is a sum of
distinct positive divisors of `n`. -/
def IsPracticalNumber (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, 1 ≤ m → m ≤ n →
    ∃ s : Finset ℕ, s ⊆ n.divisors ∧ ∑ x ∈ s, x = m

end MetaMathlibExt
