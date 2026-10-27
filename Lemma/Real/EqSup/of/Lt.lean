import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Basic.Real.Basic
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  {m M : ℝ}
-- given
  (h : m < M) :
-- imply
  sSup (Set.Ioo m M) = M :=
-- proof
  csSup_Ioo h


-- created on 2019-09-10
