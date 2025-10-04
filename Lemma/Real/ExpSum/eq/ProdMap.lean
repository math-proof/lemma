import Lemma.Real.EqExp0'1
import Lemma.Real.ExpAdd.eq.MulExpS
open Real


@[main]
private lemma main
  [Exp α]
-- given
  (l : List α) :
-- imply
  exp l.sum = (l.map Exp.exp).prod := by
-- proof
  induction l with
  | nil =>
    simp [EqExp0'1]
  | cons =>
    simp_all [ExpAdd.eq.MulExpS]


-- created on 2025-10-04
