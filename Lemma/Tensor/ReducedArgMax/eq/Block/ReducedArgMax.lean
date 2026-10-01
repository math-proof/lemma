import sympy.Basic
import sympy.concrete.expr_with_limits


@[main]
private lemma main
  [NeZero n]
  {a b : ℕ}
  {A : Fin a → Fin n → ℝ}
  {B : Fin b → Fin n → ℝ} :
-- imply
  (fun i => ArgMax Set.univ (Fin.append A B i)) = Fin.append (fun i => ArgMax Set.univ (A i)) (fun i => ArgMax Set.univ (B i)) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2021-12-20
