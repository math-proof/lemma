import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.LegendreSymbol.LinearSum
open scoped BigOperators
open legendreSym


/--
[sum_linear_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LegendreSymbol/LinearSum.lean)
-/
@[path]
private lemma sum_linear_eq_zero_eq
  {p : ℕ} [Fact p.Prime]
  {b c : ℤ}
-- given
  (hpodd : Odd p)
  (hb : ¬ (p : ℤ) ∣ b) :
-- imply
  ∑ ℓ ∈ Finset.range p, legendreSym p (b * (ℓ : ℤ) + c) = 0 := by
-- proof
  apply legendreSym.sum_linear_eq_zero p hpodd b c hb


-- created on 2026-10-20
