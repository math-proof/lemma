/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/BNomialNumberType3.lean -/

import Mathlib.Data.Fintype.Pi
import Def.NumberTheory.BNomialNumberType3
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

/-- The indispensable-digit predicate is decidable by bounded search. -/
instance decidablePredIsBNomialIndispensableDigit {n b : ℕ} (x : Fin n → Fin b) :
    DecidablePred (IsBNomialIndispensableDigit x) := by
  intro p
  unfold IsBNomialIndispensableDigit
  infer_instance

end MetaMathlibExt
