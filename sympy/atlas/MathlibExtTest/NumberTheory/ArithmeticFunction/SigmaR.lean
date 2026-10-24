/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ArithmeticFunction/SigmaR.lean -/


import sympy.atlas.NumberTheory.ArithmeticFunction.SigmaR
import Lemma.Nat.ArithmeticFunction.SigmaR

/-!
# Tests for complex-exponent divisor sums
-/


open ArithmeticFunction

example (s : ℂ) : sigmaR s 0 = 0 := by
  simp

example (s : ℂ) : sigmaR s 1 = 1 := by
  simp

example (k n : ℕ) : sigmaR (k : ℂ) n = (sigma k n : ℂ) := by
  exact sigmaR_natCast_apply k n

example (n : ℕ) : sigmaR (0 : ℂ) n = (n.divisors.card : ℂ) := by
  exact sigmaR_zero_apply n
