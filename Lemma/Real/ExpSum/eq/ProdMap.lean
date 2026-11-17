import Lemma.Real.EqExp0'1
import Lemma.Real.ExpAdd.eq.MulExpS
open Exp


@[path]
private lemma main
  [Exp α]
-- given
  (l : List α) :
-- imply
  exp l.sum = (l.map Exp.exp).prod := by
-- proof
  induction l with
  | nil =>
    simp [Real.EqExp0'1]
  | cons =>
    simp_all [Real.ExpAdd.eq.MulExpS]


-- created on 2025-10-04
-- updated on 2026-11-15
