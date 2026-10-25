/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/GarabedianBernoulliStirling.lean -/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.Rat.Star
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
open scoped BigOperators


namespace MetaMathlibExt

section

def aux_H (n : ℕ) : ℚ :=
  (n : ℚ) * ∑ j ∈ Finset.Icc 1 n,
    (((-1 : ℚ) ^ (n - j) * (Nat.factorial (j - 1) : ℚ) *
      (Nat.stirlingSecond n j : ℚ)) / (2 : ℚ) ^ (j - 1))

def aux_G (n : ℕ) : ℚ :=
  2 * (1 - (2 : ℚ) ^ n) * bernoulli n

end
end MetaMathlibExt
