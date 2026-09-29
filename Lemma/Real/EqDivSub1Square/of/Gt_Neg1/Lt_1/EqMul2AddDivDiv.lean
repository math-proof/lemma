import sympy.Basic


/--
Ellipse geometry: if the apogee and perigee distances are \(p/(1-e)\) and \(p/(1+e)\)
(\(p\) being the semi-latus rectum, \(-1<e<1\)), then
\(2a=\dfrac{p}{1-e}+\dfrac{p}{1+e}\) gives \(a=\dfrac{p}{1-e^2}\).
-/
@[main]
private lemma main
  {a e p : ℝ}
-- given
  (he₀ : -1 < e)
  (he₁ : e < 1)
  (h : 2 * a = p / (1 - e) + p / (1 + e)) :
-- imply
  a = p / (1 - e ^ 2) := by
-- proof
  have h₀ : 1 + e ≠ 0 := by linarith
  have h₁ : 1 - e ≠ 0 := by linarith
  have h₂ : 1 - e ^ 2 ≠ 0 := by nlinarith
  have : a = (p / (1 - e) + p / (1 + e)) / 2 := by linarith
  rw [this]
  field_simp [h₀, h₁, h₂]
  ring


-- created on 2026-09-29