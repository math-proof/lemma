import sympy.Basic


@[main, comm]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  s.rotate n = s.drop (n % s.length) ++ s.take (n % s.length) := by
-- proof
  apply List.rotate_eq_drop_append_take_mod


-- created on 2025-10-17
