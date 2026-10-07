import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
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
    rw [dif_pos (by omega), dif_pos h]
    exact Fin.snoc_castSucc (α := fun _ => Y) (p := ys) (x := b) (i := ⟨i, h⟩)
  ·
    rw [dif_pos (Nat.lt_succ_self _), dif_neg (lt_irrefl _)]
    exact Fin.snoc_last (α := fun _ => Y) (p := ys) (x := b)


-- created on 2026-10-07
