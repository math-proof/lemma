import sympy.Basic


@[main]
private lemma main
-- given
  (s : List α)
  (n : ℕ) :
-- imply
  s.splitAt n = ⟨s.take n, s.drop n⟩ := by
-- proof
  apply List.splitAt_eq


-- created on 2025-06-15
