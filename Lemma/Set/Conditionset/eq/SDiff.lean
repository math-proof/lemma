import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {a : α} :
-- imply
  {y : α | y ≠ a} = (Set.univ : Set α) \ {a} := by
-- proof
  ext y
  simp


-- created on 2021-02-04
