/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean -/

import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Tactic.Ring


namespace MetaMathlibExt

section

open scoped BigOperators

def ff (n k : ℕ) : ℕ → ℕ := fun j =>
  ∑ i ∈ Finset.range (k + j + 1), Nat.choose (n + j - i) i

end
end MetaMathlibExt
