import sympy.Basic


@[main, mp, mpr]
private lemma main
  [Semiring α] [PartialOrder α] [IsOrderedRing α]
  [Nontrivial α]
  {n : ℕ} :
-- imply
  (n : α) > 0 ↔ n > 0 :=
-- proof
  Nat.cast_pos


-- created on 2025-08-02
