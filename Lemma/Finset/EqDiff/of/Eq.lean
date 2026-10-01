import sympy.core.function
import sympy.Basic


@[main]
private lemma main
  {d : ℕ}
  {f g : ℤ → ℂ}
-- given
  (h : ∀ x, f x = g x) :
-- imply
  Difference f d = Difference g d := by
-- proof
  rw [funext h]


-- created on 2020-10-09
