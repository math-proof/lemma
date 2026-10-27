import Initialize.Tactic.Attr.Basic
import Macro.Order.ExprWithLimits


@[path]
private lemma main
  [NeZero n]
  {a b : ℕ}
  {A : Fin a → Fin n → ℝ}
  {B : Fin b → Fin n → ℝ} :
-- imply
  (fun i => max⁻¹ Set.univ (Fin.append A B i)) = Fin.append (fun i => max⁻¹ Set.univ (A i)) (fun i => max⁻¹ Set.univ (B i)) := by
-- proof
  funext i
  exact Fin.addCases (fun i => by simp) (fun i => by simp) i


-- created on 2021-12-20
