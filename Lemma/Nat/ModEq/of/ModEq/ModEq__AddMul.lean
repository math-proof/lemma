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
  apply h₁.trans
  have := h₀.mul_left a
  apply this.add_right b


-- created on 2025-03-15
