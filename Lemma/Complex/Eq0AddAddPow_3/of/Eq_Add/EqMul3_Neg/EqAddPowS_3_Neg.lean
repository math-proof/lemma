import sympy.Basic


@[main]
private lemma main
  {x p q A B : ℂ}
-- given
  (h₀ : A ^ 3 + B ^ 3 = -q)
  (h₁ : 3 * A * B = -p)
  (h₂ : x = A + B) :
-- imply
  x ^ 3 + p * x + q = 0 := by
-- proof
  subst h₂
  calc
    _ = A ^ 3 + B ^ 3 + 3 * A * B * (A + B) + p * (A + B) + q := by
      ring
    _ = (A ^ 3 + B ^ 3 + q) + (3 * A * B + p) * (A + B) := by
      ring
    _ = (-q + q) + (-p + p) * (A + B) := by
      rw [h₁, h₀]
    _ = 0 := by
      ring


-- created on 2026-08-28
