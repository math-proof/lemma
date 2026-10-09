import sympy.Basic


/--
Period from swept area: \(S=\dfrac{JT}{2m}\) and \(S=\pi ab\) give \(T=\dfrac{2m\pi ab}{J}\).
-/
@[path]
private lemma main
  {S T m J a b : ℝ}
-- given
  (hm : m ≠ 0)
  (hJ : J ≠ 0)
  (hS : S = J * T / (2 * m))
  (hab : S = π * a * b) :
-- imply
  T = 2 * m * π * a * b / J := by
-- proof
  rw [hab] at hS
  field_simp [hm, hJ] at hS ⊢
  linarith


-- created on 2026-09-29