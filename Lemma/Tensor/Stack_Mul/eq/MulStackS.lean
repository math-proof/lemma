import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {n : ℕ}
  {a b : ℕ → ℝ} :
-- imply
  (fun i : Fin n => a i * b i) = (fun i : Fin n => a i) * (fun i : Fin n => b i) := by
-- proof
  funext i
  rfl


-- created on 2022-06-07
-- updated on 2026-10-26
