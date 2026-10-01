import sympy.Basic


@[main]
private lemma position_representation.sinusoidal
  {d b : ℕ}
  {PE PE' : ℕ → ℕ → ℝ}
  {Z : ℕ → ℕ → ℂ}
-- given
  (h₀ : ∀ i j : ℕ, PE i j = if j % 2 = 0 then Real.sin ((i : ℝ) / (b : ℝ) ^ ((j : ℝ) / d)) else Real.cos ((i : ℝ) / (b : ℝ) ^ (((j : ℝ) - 1) / d)))
  (h₁ : ∀ i j : ℕ, PE' i j = if j % 2 = 0 then Real.cos ((i : ℝ) / (b : ℝ) ^ ((j : ℝ) / d)) else -Real.sin ((i : ℝ) / (b : ℝ) ^ (((j : ℝ) - 1) / d)))
  (h₂ : ∀ i j : ℕ, Z i j = Complex.I * PE i j - PE' i j) :
-- imply
  ∀ i j : ℕ, Z i j = Complex.exp (Complex.I * ((Real.pi / 2 * (2 - ((j % 2 : ℕ) : ℝ)) - (i : ℝ) / (b : ℝ) ^ (((2 * (j / 2) : ℕ) : ℝ) / d) : ℝ) : ℂ)) := by
-- proof
  intro i j
  have key : ∀ r : ℝ, Complex.exp (Complex.I * (r : ℂ)) = (Real.cos r : ℂ) + (Real.sin r : ℂ) * Complex.I := by
    intro r
    rw [mul_comm, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [h₂, h₀, h₁, key]
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  ·
    have e : 2 * (j / 2) = j := by omega
    have r : Real.pi / 2 * (2 - ((j % 2 : ℕ) : ℝ)) - (i : ℝ) / (b : ℝ) ^ (((2 * (j / 2) : ℕ) : ℝ) / d) = Real.pi - (i : ℝ) / (b : ℝ) ^ ((j : ℝ) / d) := by
      rw [hj, e]
      push_cast
      ring
    rw [r, Real.cos_pi_sub, Real.sin_pi_sub, if_pos hj, if_pos hj]
    push_cast
    ring
  ·
    have e : 2 * (j / 2) = j - 1 := by omega
    have r : Real.pi / 2 * (2 - ((j % 2 : ℕ) : ℝ)) - (i : ℝ) / (b : ℝ) ^ (((2 * (j / 2) : ℕ) : ℝ) / d) = Real.pi / 2 - (i : ℝ) / (b : ℝ) ^ (((j : ℝ) - 1) / d) := by
      rw [hj, e, Nat.cast_sub (by omega : 1 ≤ j)]
      push_cast
      ring
    have hj' : ¬j % 2 = 0 := by omega
    rw [r, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, if_neg hj', if_neg hj']
    push_cast
    ring


-- created on 2026-09-27
