import sympy.Basic


@[main]
private lemma main
  {n a b y x x₀ : ℕ}
-- given
  (h₀ : x ≡ x₀ [MOD n])
  (h₁ : y ≡ a * x + b [MOD n]) :
-- imply
  y ≡ a * x₀ + b [MOD n] := by
-- proof
  have := h₀.mul_left a
  have := this.add_right b
  exact h₁.trans this


-- created on 2025-03-15
