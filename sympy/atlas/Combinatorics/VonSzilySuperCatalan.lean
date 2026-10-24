/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean -/

import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open scoped BigOperators

section
namespace MetaMathlibExt

/-- If-form binomial: genuinely 0 for negative index (unlike toNat form). -/
private def wzB (N : ℕ) (t : ℤ) : ℚ := if 0 ≤ t then ((Nat.choose N t.toNat : ℕ) : ℚ) else 0

private def wzE (M N : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * wzB (2 * M) ((M : ℤ) + k) * wzB (2 * N) ((N : ℤ) + k)

private def wzElow (M N : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * wzB (2 * M - 2) (((M : ℤ) - 1) + k) * wzB (2 * N) ((N : ℤ) + k)

private def wzG (M N : ℕ) (j : ℤ) : ℚ :=
  (-1 : ℚ) ^ (j + 1) * wzB (2 * M - 1) ((M : ℤ) - j) * (2 * (N : ℚ)) *
    wzB (2 * N - 1) ((N : ℤ) - j)

/-- If-form summatory function. -/
private def wzF (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))), wzE m n k
end MetaMathlibExt
