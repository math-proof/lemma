/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/RParameterGeneralizedFibonacciSequence.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
open scoped BigOperators

/-!
# Barry–Hennessy generalized Fibonacci numbers

The definition is the general term in Paul Barry and Aoife Hennessy,
*Notes on a Family of Riordan Arrays and Associated Integer Hankel
Transforms*, Journal of Integer Sequences 12 (2009), Article 09.5.3.
-/


namespace MetaMathlibExt

/-- The Barry–Hennessy `r`-parameter generalized Fibonacci number
`sum k = 0..floor(n/2), choose (n-k) k * r^k`.

Stable source identifiers: concept `jis_sem_7e39b379c7c56d484f5a68a4`,
statement `jis_7e39b379c7c56d484f5a68a4`.
-/
def rFibonacciNumber (r : ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (n / 2 + 1), (Nat.choose (n - k) k : ℝ) * r ^ k

end MetaMathlibExt
