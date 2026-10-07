import sympy.sets.fancysets
import sympy.Basic


@[main]
private lemma main
  {a b k : ℤ}
-- given
  (hk : k ≠ 0) :
-- imply
  Range a b k = Range (b - k.sign - ((b - k.sign) - a) % k) (a - k.sign) (-k) := by
-- proof
  sorry


-- created on 2026-10-07
