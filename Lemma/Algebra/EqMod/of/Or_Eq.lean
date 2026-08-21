import sympy.Basic


@[main]
private lemma main
  {x a d : ℤ}
-- given
  (h : x = a ∨ x = a + d) :
-- imply
  x % d = a % d := by
-- proof
  rcases h with h | h
  ·
    rw [h]
  ·
    rw [h, Int.add_emod_right]


-- created on 2018-11-22
-- updated on 2026-08-20
