import Syntax.Order.ExprWithLimits
import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [NeZero (n : ℕ)]
  {f : ℕ → ℝ} :
-- imply
  «min⁻¹» (Set.univ : Set (Fin n)) (fun i => f i) = «max⁻¹» Set.univ (fun i : Fin n => -f ↑i) := by
-- proof
  unfold «min⁻¹» «max⁻¹»
  congr 1
  funext k
  simp only [neg_le_neg_iff]


-- created on 2023-11-05
-- updated on 2026-11-13
