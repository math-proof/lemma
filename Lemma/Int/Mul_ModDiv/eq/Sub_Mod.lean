import Theorem.Data.Set.Sets
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {x d : ℤ} :
-- imply
  Int.fdiv x d * d = x - Int.fmod x d := by
-- proof
  rw [Int.fmod_def]
  ring


-- created on 2020-01-28
