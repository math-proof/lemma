import sympy.Basic


@[path]
private lemma bert.position_representation.relative
  {n d_z : ℕ}
  {Q K V : Fin n → Fin d_z → ℝ}
  {K' V' : Fin n → Fin n → Fin d_z → ℝ}
  {c : ℤ}
  {wK wV : ℤ → Fin d_z → ℝ}
-- given
  (h₀ : ∀ i j t, K' i j t = wK (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)
  (h₁ : ∀ i j t, V' i j t = wV (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t) :
-- imply
  ∀ (i : Fin n) (s : Fin d_z), ∑ j, Real.exp ((∑ t, Q i t * (K j t + K' i j t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K k t + K' i k t)) / √d_z)) * (V j s + V' i j s) =
    ∑ j, Real.exp ((∑ t, Q i t * (K j t + wK (c + max (-c) (min ((j.val : ℤ) - i.val) c)) t)) / √d_z) / (∑ k, Real.exp ((∑ t, Q i t * (K k t + wK (c + max (-c) (min ((k.val : ℤ) - i.val) c)) t)) / √d_z)) * (V j s + wV (c + max (-c) (min ((j.val : ℤ) - i.val) c)) s) := by
-- proof
  intro i s
  simp only [h₀, h₁]


-- created on 2026-09-27
