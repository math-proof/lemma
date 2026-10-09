import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[path]
private lemma main
  {t : ℕ}
-- given
  (h : t < t + 1)
  (ys : Fin t → Y)
  (b : Y) :
-- imply
  Fin.snoc (α := fun _ => Y) ys b ⟨t, h⟩ = b := by
-- proof
  exact Fin.snoc_last (α := fun _ => Y) (p := ys) (x := b)


-- created on 2026-10-07
