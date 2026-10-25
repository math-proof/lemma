import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Divisors
import Lemma.ModularCurve.X0

namespace ModularCurve

noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

def cuspCount (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, Nat.totient (Nat.gcd d (N / d))


noncomputable def genusFormula (N : ℕ) : ℚ :=
  1 + (dedekindPsi N : ℚ) / 12 - (nuTwo N : ℚ) / 4 - (nuThree N : ℚ) / 3
    - (cuspCount N : ℚ) / 2

end ModularCurve
