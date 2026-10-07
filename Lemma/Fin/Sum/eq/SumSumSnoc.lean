import sympy.stats.hidden_markov_sequence
import sympy.Basic


@[main]
private lemma main
  [Fintype Y]
  {t : ℕ}
-- given
  (F : (Fin (t + 1) → Y) → ℝ) :
-- imply
  ∑ ys, F ys = ∑ b, ∑ ys0 : Fin t → Y, F (Fin.snoc (α := fun _ => Y) ys0 b) := by
-- proof
  rw [← (Fin.snocEquiv (fun _ => Y)).sum_comp, Fintype.sum_prod_type]
  rfl


-- created on 2026-10-07
