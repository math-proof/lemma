/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Bernoulli/KanekoBernoulliStirling.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Rat.Star


namespace MetaMathlibExt

noncomputable def kanekoT (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1), (-1 : ℚ) ^ j * (j.factorial : ℚ)
    * (Nat.stirlingSecond n j : ℚ) / ((j : ℚ) + 1)

end MetaMathlibExt
