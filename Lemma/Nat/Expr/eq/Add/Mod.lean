import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x d : ℤ} :
-- imply
  x = Int.fdiv x d * d + Int.fmod x d := by
-- proof
  rw [Int.fmod_def]
  ring


-- created on 2023-06-04
