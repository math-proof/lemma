import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {a b c : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : b < c) :
-- imply
  a < c := by
-- proof
  rwa [h₀]


@[main]
private lemma relax
  {a b d : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : b < d) :
-- imply
  a < d := by
-- proof
  rwa [h₀]


@[main]
private lemma relax.lower
  {a b c : ℝ}
-- given
  (h₀ : a = b)
  (h₁ : c < b) :
-- imply
  c < a := by
-- proof
  rwa [h₀]


-- created on 2026-09-27
