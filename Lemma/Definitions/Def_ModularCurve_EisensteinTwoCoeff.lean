import Mathlib.NumberTheory.Divisors

namespace ModularCurve

def sigmaPrimeTo (p n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), d

def eisensteinTwoCoeff (p n : ℕ) : ℤ := if n = 0 then (p : ℤ) - 1 else 24 * (sigmaPrimeTo p n : ℤ)

theorem eisensteinTwoCoeff_zero (p : ℕ) : eisensteinTwoCoeff p 0 = (p : ℤ) - 1 := by
  simp [eisensteinTwoCoeff]

theorem eisensteinTwoCoeff_of_ne_zero (p : ℕ) {n : ℕ} (hn : n ≠ 0) :
    eisensteinTwoCoeff p n = 24 * (sigmaPrimeTo p n : ℤ) := by
  simp [eisensteinTwoCoeff, hn]

example : eisensteinTwoCoeff 11 0 = 10 := by decide
example : eisensteinTwoCoeff 11 1 = 24 := by decide
example : eisensteinTwoCoeff 11 2 = 72 := by decide
example : eisensteinTwoCoeff 11 11 = 24 := by decide
example : eisensteinTwoCoeff 11 22 = 72 := by decide
example : eisensteinTwoCoeff 2 0 = 1 := by decide
example : eisensteinTwoCoeff 2 4 = 24 := by decide

end ModularCurve
