/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BNomialNumberType3.lean -/

import Mathlib.Data.Fintype.Pi
/-!
# Type-3 b-nomial numbers

For a base `b ≥ 2`, Ji Young Choi defines a digit in a finite `b`-ary string to be
*indispensable* when it belongs to a constant run whose next digit to the right is smaller.
The type-3 `b`-nomial number counts length-`n` strings having exactly `k` indispensable digits.

Source: Ji Young Choi, *Digit Sums Generalizing Binomial Coefficients*,
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Choi/choi15.tex>, the definitions of
indispensable digits and type-3 `b`-nomial numbers.

JIS concept: `jis_sem_c0908e8c24b869247eba442f`.
-/


namespace MetaMathlibExt

/-- The digit in position `j` of a `b`-ary string, extended by zero to its right.

Positions in `x` run from left to right, so `x 0` represents the source's leftmost digit
`a_n`. In particular, position `n` represents the stipulated boundary digit `a_0 = 0`. -/
def bNomialDigitAtOrZero {n b : ℕ} (x : Fin n → Fin b) (j : ℕ) : ℕ :=
  if h : j < n then (x ⟨j, h⟩).val else 0

/-- A position is indispensable when some nonempty constant run beginning there is followed
on the right by a strictly smaller digit.

The paper prints the witness bound `r ≤ i + 1`, although only the boundary digit `a₀` is
defined. With the right-zero extension above, that final nominal case is unsatisfiable and the
predicate agrees with all source-defined cases. -/
def IsBNomialIndispensableDigit {n b : ℕ} (x : Fin n → Fin b) (p : Fin n) : Prop :=
  ∃ r : Fin (n + 2),
    1 ≤ r.val ∧
      p.val + r.val ≤ n + 1 ∧
      (∀ t : Fin (n + 2), 1 ≤ t.val → t.val < r.val →
        bNomialDigitAtOrZero x (p.val + t.val) = (x p).val) ∧
      bNomialDigitAtOrZero x (p.val + r.val) < (x p).val

end MetaMathlibExt
