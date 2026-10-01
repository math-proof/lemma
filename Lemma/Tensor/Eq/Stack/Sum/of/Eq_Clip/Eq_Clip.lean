import sympy.Basic


@[main]
private lemma position_representation.relative
  {n d_z : ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
-- given
  (_h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)
  (_h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t) :
-- imply
  ∀ (i : Fin n) (s : Fin d_z), ∑ j, Real.exp ((∑ t, Q i t * (K j t + K' i j t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K k t + K' i k t)) / √d_z)) * (V j s + V' i j s) =
    (∑ j, (V j s + V' i j s) * Real.exp ((∑ t, Q i t * (K j t + K' i j t)) / √d_z)) / (∑ k, Real.exp ((∑ t, Q i t * (K k t + K' i k t)) / √d_z)) := by
-- proof
  intro i s
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun j _ => by ring


-- created on 2026-09-27
