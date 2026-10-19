import sympy.stats.hidden_markov_sequence


@[path]
private lemma main
  {t i : ℕ}
-- given
  (hi : i ≤ t)
  (ys : Fin t → Y)
  (b a : Y) :
-- imply
  (if h : i < t + 1 then Fin.snoc (α := fun _ => Y) ys b ⟨i, h⟩ else a) = if h : i < t then ys ⟨i, h⟩ else b := by
-- proof
  obtain h | rfl := hi.lt_or_eq
  ·
    rw [dite_eq_left (by omega), dite_eq_left h]
    exact Fin.snoc_castSucc (α := fun _ => Y) (p := ys) (x := b) (i := ⟨i, h⟩)
  ·
    rw [dite_eq_left (Nat.lt_succ_self _), dite_eq_right (lt_irrefl _)]
    exact Fin.snoc_last (α := fun _ => Y) (p := ys) (x := b)


-- created on 2026-10-07
