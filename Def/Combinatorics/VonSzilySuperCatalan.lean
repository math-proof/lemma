/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VonSzilySuperCatalan.lean -/

module

public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Data.Int.Star
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

open scoped BigOperators


section

namespace MetaMathlibExt

/-- If-form binomial: genuinely 0 for negative index (unlike toNat form). -/
def wzB (N : ℕ) (t : ℤ) : ℚ := if 0 ≤ t then ((Nat.choose N t.toNat : ℕ) : ℚ) else 0

def wzE (M N : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * wzB (2 * M) ((M : ℤ) + k) * wzB (2 * N) ((N : ℤ) + k)

def wzElow (M N : ℕ) (k : ℤ) : ℚ :=
  (-1 : ℚ) ^ k * wzB (2 * M - 2) (((M : ℤ) - 1) + k) * wzB (2 * N) ((N : ℤ) + k)

def wzG (M N : ℕ) (j : ℤ) : ℚ :=
  (-1 : ℚ) ^ (j + 1) * wzB (2 * M - 1) ((M : ℤ) - j) * (2 * (N : ℚ)) *
    wzB (2 * N - 1) ((N : ℤ) - j)

/-- If-form summatory function. -/
def wzF (m n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc (max (-(m : ℤ)) (-(n : ℤ))) (min ((m : ℤ)) ((n : ℤ))), wzE m n k

end MetaMathlibExt
end
