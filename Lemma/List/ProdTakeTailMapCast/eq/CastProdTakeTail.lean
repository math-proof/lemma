import sympy.Basic


@[main]
private lemma main
  [Ring α]
-- given
  (s : List ℕ)
  (i : ℕ) :
-- imply
  ((s.map (Nat.cast (R := α))).tail.take i).prod = (s.tail.take i).prod := by
-- proof
  simp [List.map_take]


-- created on 2025-11-14
