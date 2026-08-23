import sympy.functions.elementary.integers
import sympy.Basic


@[main]
private lemma main
  [IntegerRing Z]
  {x a d : Z}
-- given
  (h : x = a ∨ x = a + d) :
-- imply
  x % d = a % d := by
-- proof
  rcases h with h | h
  ·
    rw [h]
  ·
    rw [h]
    simpa [one_mul] using IntegerRing.add_mul_mod_self_right a 1 d


-- created on 2018-11-22
-- updated on 2026-08-23
