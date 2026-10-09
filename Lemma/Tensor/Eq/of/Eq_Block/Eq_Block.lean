import sympy.Basic


@[path]
private lemma relative_distance.upper_triangle
  {n u : ℕ}
  {k : ℤ}
  {w : ℤ → ℝ}
  {r : ℕ → ℤ}
  {V V' : ℕ → ℕ → ℝ}
-- given
  (h₀ : ∀ i j, V i j = w (k + max (-k) (min (r j - r i) k)))
  (h₁ : ∀ i j, V' i j = w (k + max (-k) (min (r (min (n - 1) (i + j)) - r i) k))) :
-- imply
  ∀ i j, i < n → i ≤ j → j < n → j < i + u → V i j = V' i (j - i) := by
-- proof
  intro i j _hi hij hj _hu
  have hmin : min (n - 1) (i + (j - i)) = j := by omega
  rw [h₀, h₁, hmin]


@[path]
private lemma relative_distance.lower_triangle
  {n l : ℕ}
  {k : ℤ}
  {w : ℤ → ℝ}
  {r : ℕ → ℤ}
  {V V' : ℕ → ℕ → ℝ}
-- given
  (h₀ : ∀ i j, V i j = w (k + max (-k) (min (r j - r i) k)))
  (h₁ : ∀ i j, V' i j = w (k + max (-k) (min (r (min (n - 1) (j + (i + 1 - l))) - r i) k))) :
-- imply
  ∀ i j, i < n → i + 1 - l ≤ j → j ≤ i → V i j = V' i (j - (i + 1 - l)) := by
-- proof
  intro i j hi hlj hji
  have hmin : min (n - 1) (j - (i + 1 - l) + (i + 1 - l)) = j := by omega
  rw [h₀, h₁, hmin]


-- created on 2026-09-27
