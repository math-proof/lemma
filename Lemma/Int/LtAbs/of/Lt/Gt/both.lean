import Mathlib.Data.Int.Basic
import sympy.Basic


@[main]
private lemma main
  {x y : ℤ}
  -- given
  (h1 : x < y)
  (h2 : -y < x)
  -- imply
  : |x| < y := by
  -- proof
  rw [abs_lt]
  exact ⟨h2, h1⟩

-- created on 2019-05-30
