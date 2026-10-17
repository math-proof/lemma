import sympy.Basic


@[path]
private lemma main
  {a b c d : ℤ}
  {p : ℤ → Prop} :
-- imply
  (∃ i ∈ ({a, b, c, d} : Set ℤ), p i) ↔ p a ∨ p b ∨ p c ∨ p d := by
-- proof
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, exists_eq_or_imp, exists_eq_left]


-- created on 2026-10-11
-- updated on 2026-10-17
