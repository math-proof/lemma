import sympy.Basic


@[main]
private lemma relative_distance.upper_triangle.upper_part
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + i) (n - 1)) - r i) (k : ℤ)))) :
-- imply
  ∀ i < n - u, ∀ j < u, V i (i + j) = V' i j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + i) (n - 1) = i + j by omega]


@[main]
private lemma relative_distance.upper_triangle.lower_part
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + i) (n - 1)) - r i) (k : ℤ))))
  (h₂ : u ≤ n) :
-- imply
  ∀ i < u, ∀ j < u - i, V (i + n - u) (i + n - u + j) = V' (i + n - u) j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + (i + n - u)) (n - 1) = i + n - u + j by omega]


@[main]
private lemma relative_distance.lower_triangle.lower_part
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + (i + 1 - u)) (n - 1)) - r i) (k : ℤ)))) :
-- imply
  ∀ i < n - u, ∀ j < u, V (i + u) (i + 1 + j) = V' (i + u) j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + (i + u + 1 - u)) (n - 1) = i + 1 + j by omega]


@[main]
private lemma relative_distance.lower_triangle.upper_part
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + (i + 1 - u)) (n - 1)) - r i) (k : ℤ))))
  (h₂ : u ≤ n) :
-- imply
  ∀ i < u, ∀ j ≤ i, V i j = V' i j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + (i + 1 - u)) (n - 1) = j by omega]


@[main]
private lemma relative_distance.lower_triangle.lower_part.tf
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + (i + 1 - u)) (n - 1)) - r i) (k : ℤ))))
  (h₂ : 1 ≤ u)
  (h₃ : u ≤ n) :
-- imply
  ∀ i < n - u + 1, ∀ j < u, V (i + u - 1) (i + j) = V' (i + u - 1) j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + (i + u - 1 + 1 - u)) (n - 1) = i + j by omega]


@[main]
private lemma relative_distance.lower_triangle.upper_part.tf
  {n u k : ℕ}
  {r : ℕ → ℤ}
  {w : ℤ → α}
  {V V' : ℕ → ℕ → α}
-- given
  (h₀ : ∀ i j, V i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r j - r i) (k : ℤ))))
  (h₁ : ∀ i j, V' i j = w ((k : ℤ) + max (-(k : ℤ)) (min (r (min (j + (i + 1 - u)) (n - 1)) - r i) (k : ℤ))))
  (h₂ : u ≤ n) :
-- imply
  ∀ i < u - 1, ∀ j ≤ i, V i j = V' i j := by
-- proof
  intro i hi j hj
  rw [h₀, h₁, show min (j + (i + 1 - u)) (n - 1) = j by omega]


-- created on 2026-09-27
