/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/FilipponiBinomialSum.lean -/

module

public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Tactic.Ring

@[expose] public section

namespace MetaMathlibExt

section

open scoped BigOperators

def ff (n k : ℕ) : ℕ → ℕ := fun j =>
  ∑ i ∈ Finset.range (k + j + 1), Nat.choose (n + j - i) i

end
end MetaMathlibExt
