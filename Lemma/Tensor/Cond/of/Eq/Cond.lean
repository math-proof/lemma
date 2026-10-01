import sympy.Basic


@[main]
private lemma subs_with_expand_dims
  {m n : ℕ}
  {a : Fin n → ℝ}
  {b c : Fin m → Fin n → ℝ}
  {S : Set (Fin m → Fin n → ℝ)}
-- given
  (h₀ : (fun (_ : Fin m) j => a j) = c)
  (h₁ : (fun i j => a j * b i j) ∈ S) :
-- imply
  (fun i j => c i j * b i j) ∈ S := by
-- proof
  rw [← h₀]
  exact h₁


-- created on 2026-09-27
