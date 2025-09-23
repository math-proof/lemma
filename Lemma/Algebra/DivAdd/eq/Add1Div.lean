import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Div.eq.One.of.Ne_0
open Algebra


@[main]
private lemma main
  [DivisionSemiring α]
  {x d : α}
-- given
  (h : d ≠ 0) :
-- imply
  (d + x) / d = 1 + x / d := by
-- proof
  rw [DivAdd.eq.AddDivS]
  rw [Div.eq.One.of.Ne_0 h]


-- created on 2025-03-25
