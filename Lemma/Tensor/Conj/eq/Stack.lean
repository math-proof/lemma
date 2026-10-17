import sympy.Basic


@[path]
private lemma main
  {n : ℕ}
  {h : Fin n → ℂ} :
-- imply
  ∀ i, starRingEnd ℂ (h i * Complex.I) = starRingEnd ℂ (h i) * (-Complex.I) := by
-- proof
  intro i
  simp [map_mul, Complex.conj_I]


-- created on 2026-10-11
-- updated on 2026-10-17
