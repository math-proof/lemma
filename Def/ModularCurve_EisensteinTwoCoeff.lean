import Mathlib.NumberTheory.Divisors

namespace ModularCurve

def sigmaPrimeTo (p n : ℕ) : ℕ := ∑ d ∈ n.divisors.filter (fun d => ¬ p ∣ d), d

def eisensteinTwoCoeff (p n : ℕ) : ℤ := if n = 0 then (p : ℤ) - 1 else 24 * (sigmaPrimeTo p n : ℤ)

end ModularCurve
