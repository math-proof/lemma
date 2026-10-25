/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BNomialNumberType3.lean -/

import Mathlib.Data.Fintype.Pi
import Instance.NumberTheory.BNomialNumberType3
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

/-- The number `ι(x)` of indispensable digits in a finite `b`-ary string. -/
def bNomialIndispensableDigitCount {n b : ℕ} (x : Fin n → Fin b) : ℕ :=
  Fintype.card { p : Fin n // IsBNomialIndispensableDigit x p }

/-- The type-3 `b`-nomial number: the number of length-`n` `b`-ary strings with exactly
`k` indispensable digits. The source convention at `n = 0` follows automatically: the
value is one at `k = 0` and zero otherwise. -/
def bNomialNumberType3 (b : ℕ) (_hb : 2 ≤ b) (n : ℕ) (k : ℤ) : ℕ :=
  Fintype.card { x : Fin n → Fin b // (bNomialIndispensableDigitCount x : ℤ) = k }

end MetaMathlibExt
