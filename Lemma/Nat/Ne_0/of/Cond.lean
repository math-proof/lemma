import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma given
  {p : Prop} [Decidable p]
-- given
  (h : p) :
-- imply
  (if p then 1 else 0 : ℤ) ≠ 0 := by
-- proof
  simp [ite_eq_left h]


-- created on 2023-11-05
