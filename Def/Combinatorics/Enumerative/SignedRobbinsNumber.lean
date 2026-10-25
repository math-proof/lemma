/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/SignedRobbinsNumber.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
open scoped BigOperators

/-!
# Signed Robbins numbers

The definitions in this file come from Paul Barry, *From Fibonacci to Robbins:
Series Reversion and Hankel Transforms*, Journal of Integer Sequences 24 (2021).
-/


namespace MetaMathlibExt

/-- The Robbins number
`Aₙ = (∏ k < n, (3k + 1)!) / (∏ k < n, (n + k)!)`.

Stable source identifiers: concept `jis_sem_6ccc916178dd254f612035dd`;
source statements `jis_43e90ede434b32aa20186bc5`,
`jis_6d15f998fcbd06c902185831`, `jis_8997a72d034e17ed46810fce`,
`jis_9e6db18aea1f87c47362e55f`, and `jis_f49a3ed20d503c088eb53ef1`.
-/
def robbinsNumber (n : ℕ) : ℕ :=
  (∏ k ∈ Finset.range n, (3 * k + 1).factorial) /
    (∏ k ∈ Finset.range n, (n + k).factorial)

/-- The signed Robbins sequence `(-1) ^ choose (n + 1) 2 * A_(n+1)`. -/
def signedRobbinsNumber (n : ℕ) : ℤ :=
  (-1) ^ Nat.choose (n + 1) 2 * (robbinsNumber (n + 1) : ℤ)

end MetaMathlibExt
