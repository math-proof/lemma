/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KanekoBernoulliStirling.lean -/

module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Rat.Star

@[expose] public section

namespace MetaMathlibExt

noncomputable def kanekoT (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
    * (Nat.stirlingSecond n j : ℚ) / ((j : ℚ) + 1)

end MetaMathlibExt
