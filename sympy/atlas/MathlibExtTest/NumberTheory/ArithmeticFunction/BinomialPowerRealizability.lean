/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/BinomialPowerRealizability.lean -/


import sympy.atlas.NumberTheory.ArithmeticFunction.BinomialPowerRealizability
import Lemma.Nat.ArithmeticFunction.BinomialPowerRealizability

/-!
# Tests for binomial-power sequences

Value tests for `binomialPowerSeq` at Apéry (`r = s = 2`), central
Delannoy (`r = s = 1`), and Franel (`s = 0`) parameters, plus the
`n = 0` endpoint, `r`/`s` ordering, and zero exponents.
-/

namespace MetaMathlibExt

-- Apéry numbers: `r = s = 2`.
example : binomialPowerSeq 2 2 0 = 1 := by rfl
example : binomialPowerSeq 2 2 1 = 5 := by rfl
example : binomialPowerSeq 2 2 2 = 73 := by rfl
example : binomialPowerSeq 2 2 3 = 1445 := by rfl

-- Central Delannoy numbers: `r = s = 1`.
example : binomialPowerSeq 1 1 0 = 1 := by rfl
example : binomialPowerSeq 1 1 1 = 3 := by rfl
example : binomialPowerSeq 1 1 2 = 13 := by rfl
example : binomialPowerSeq 1 1 3 = 63 := by rfl

-- Franel numbers of order 2: `r = 2`, `s = 0`.
example : binomialPowerSeq 2 0 0 = 1 := by rfl
example : binomialPowerSeq 2 0 1 = 2 := by rfl
example : binomialPowerSeq 2 0 2 = 6 := by rfl
example : binomialPowerSeq 2 0 3 = 20 := by rfl

-- Franel numbers of order 3: `r = 3`, `s = 0`.
example : binomialPowerSeq 3 0 0 = 1 := by rfl
example : binomialPowerSeq 3 0 1 = 2 := by rfl
example : binomialPowerSeq 3 0 2 = 10 := by rfl
example : binomialPowerSeq 3 0 3 = 56 := by rfl

-- Powers of two: `r = 1`, `s = 0`.
example : binomialPowerSeq 1 0 0 = 1 := by rfl
example : binomialPowerSeq 1 0 1 = 2 := by rfl
example : binomialPowerSeq 1 0 2 = 4 := by rfl
example : binomialPowerSeq 1 0 3 = 8 := by rfl

-- Range endpoint: `n = 0` gives `1` for any `r` and `s`.
example : binomialPowerSeq 0 0 0 = 1 := by rfl
example : binomialPowerSeq 3 7 0 = 1 := by rfl
example : binomialPowerSeq 0 3 0 = 1 := by rfl

-- `r`/`s` ordering matters: swapping gives different values.
example : binomialPowerSeq 1 2 1 = 5 := by rfl
example : binomialPowerSeq 2 1 1 = 3 := by rfl
example : binomialPowerSeq 1 2 2 = 55 := by rfl
example : binomialPowerSeq 2 1 2 = 19 := by rfl

-- Zero exponents.
example : binomialPowerSeq 0 0 2 = 3 := by rfl
example : binomialPowerSeq 0 0 3 = 4 := by rfl
example : binomialPowerSeq 0 1 1 = 3 := by rfl
example : binomialPowerSeq 0 1 2 = 10 := by rfl
example : binomialPowerSeq 0 2 1 = 5 := by rfl

-- The headline theorem applies at Apéry parameters.
example : doldRealizable (fun n => ((binomialPowerSeq 2 2 n : ℕ) : ℤ)) :=
  binomial_power_sequence_dold_realizable 2 2 (by decide)

#print axioms binomial_power_sequence_dold_realizable

end MetaMathlibExt
