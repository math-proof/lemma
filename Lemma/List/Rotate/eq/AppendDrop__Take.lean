import sympy.Basic


@[main, comm]
private lemma main
  -- given
  (v : List α)
  (n : ℕ) :
-- imply
  v.rotate n = v.drop (n % v.length) ++ v.take (n % v.length) := by
-- proof
  apply List.rotate_eq_drop_append_take_mod


-- created on 2025-10-17
