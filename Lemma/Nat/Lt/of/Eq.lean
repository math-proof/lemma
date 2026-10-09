import sympy.sets.sets
import sympy.Basic


@[path]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : b < c) :
-- imply
  a < c := by
-- proof
  rwa [h₀]


@[path]
private lemma relax
  {a b d : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : b < d) :
-- imply
  a < d := by
-- proof
  rwa [h₀]


@[path]
private lemma relax.lower
  {a b c : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : c < b) :
-- imply
  c < a := by
-- proof
  rwa [h₀]


-- created on 2021-08-24
