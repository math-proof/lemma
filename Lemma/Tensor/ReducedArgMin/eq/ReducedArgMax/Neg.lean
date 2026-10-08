import sympy.concrete.expr_with_limits
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
  {n : ℕ} [NeZero n]
  {f : ℕ → ℝ} :
-- imply
  ArgMin (Set.univ : Set (Fin n)) (fun i => f i) = ArgMax Set.univ (fun i : Fin n => -f ↑i) := by
-- proof
  unfold ArgMin ArgMax
  congr 1
  funext k
  simp only [neg_le_neg_iff]


-- created on 2026-10-08
