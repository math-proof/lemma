import Mathlib.Algebra.Order.Field.Basic
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {t x a b : ℝ}
-- given
  (h₀ : t < 0)
  (h₁ : x ∈ Ioc a b) :
-- imply
  x / t ∈ Ico (b / t) (a / t) :=
-- proof
  ⟨div_le_div_of_nonpos_of_le h₀.le h₁.2, div_lt_div_of_neg_of_lt h₀ h₁.1⟩


-- created on 2026-09-26
