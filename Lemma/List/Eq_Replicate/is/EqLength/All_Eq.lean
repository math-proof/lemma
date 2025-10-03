import sympy.Basic


@[main, mp, mpr]
private lemma main
-- given
  (l : List α)
  (n : ℕ)
  (a : α) :
-- imply
  l = List.replicate n a ↔ l.length = n ∧ ∀ b ∈ l, b = a :=
-- proof
  List.eq_replicate_iff


-- created on 2025-08-02
