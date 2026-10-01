import sympy.Basic


@[main]
private lemma unshift
  {a b : ℤ}
  {g : ℤ → Prop}
-- given
  (h₀ : g (a - 1))
  (h₁ : ∀ k, a ≤ k → k < b → g k) :
-- imply
  ∀ k, a - 1 ≤ k → k < b → g k := by
-- proof
  intro k hk₀ hk₁
  rcases eq_or_lt_of_le hk₀ with h | h
  ·
    rw [← h]
    exact h₀
  ·
    exact h₁ k (by omega) hk₁


@[main]
private lemma push
  {a b : ℤ}
  {g : ℤ → Prop}
-- given
  (h₀ : g b)
  (h₁ : ∀ k, a ≤ k → k < b → g k) :
-- imply
  ∀ k, a ≤ k → k < b + 1 → g k := by
-- proof
  intro k hk₀ hk₁
  rcases lt_or_eq_of_le (Int.lt_add_one_iff.mp hk₁) with h | h
  ·
    exact h₁ k hk₀ h
  ·
    rw [h]
    exact h₀


-- created on 2019-03-12
