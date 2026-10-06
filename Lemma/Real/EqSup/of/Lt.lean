import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Basic
import sympy.Basic


@[main]
private lemma main
  {m M : ℝ}
-- given
  (h : m < M) :
-- imply
  sSup (Set.Ioo m M) = M :=
-- proof
  csSup_Ioo h


-- created on 2019-09-10
