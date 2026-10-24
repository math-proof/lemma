/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LegendreSymbol/LinearSum.lean -/

/-
# Tests for linear sums of Legendre symbols
-/

import Lemma.Nat.LegendreSymbol.LinearSum


open scoped BigOperators

example (p : ℕ) [Fact p.Prime] (hpodd : Odd p) (b c : ℤ) (hb : ¬ (p : ℤ) ∣ b) :
    ∑ ℓ ∈ Finset.range p, legendreSym p (b * (ℓ : ℤ) + c) = 0 :=
  legendreSym.sum_linear_eq_zero p hpodd b c hb
