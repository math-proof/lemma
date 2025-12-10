import Lemma.Int.GeAbs
open Int


@[main]
private lemma main
  [AddGroup α]
  [LinearOrder α]
-- given
  (a : α) :
-- imply
  |a| ≥ -a := by
-- proof
  have := GeAbs (-a)
  simp at this
  assumption


-- created on 2025-12-10
