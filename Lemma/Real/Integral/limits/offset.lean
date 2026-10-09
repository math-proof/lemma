import sympy.integrals.integrals
import sympy.Basic


@[path]
private lemma main
  {a b d : ℝ}
  {f : ℝ → ℝ} :
-- imply
  ∫ x : ℝ in a..b, f x = ∫ x : ℝ in (a - d)..(b - d), f (x + d) := by
-- proof
  simp


-- created on 2020-06-05
-- updated on 2023-05-20
