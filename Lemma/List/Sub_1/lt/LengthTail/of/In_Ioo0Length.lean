import sympy.sets.sets
import Lemma.Algebra.LtSubS.of.Lt.Le
open Algebra


@[main]
private lemma main
  {i : ℕ}
  {s : List α}
-- given
  (h : i ∈ Ioo 0 s.length) :
-- imply
  i - 1 < s.tail.length := by
-- proof
  simp
  apply LtSubS.of.Lt.Le h.1 h.2


-- created on 2025-06-22
-- updated on 2025-10-10
