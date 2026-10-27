import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  {p : Prop} [Decidable p]
-- given
  (h : p) :
-- imply
  (if p then (1 : ℝ) else 0) > 0 := by
-- proof
  rw [ite_eq_left h]
  norm_num


-- created on 2023-11-05
