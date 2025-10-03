import sympy.vector.vector
import Lemma.Algebra.Ge.of.NotLt
import Lemma.List.GetElem!Range.eq.None.of.Ge
open Algebra List


@[main, mp, mpr]
private lemma main
-- given
  (n i j : ℕ) :
-- imply
  (List.range n)[i]? = some j ↔ i < n ∧ i = j := by
-- proof
  by_cases hi : i < n <;>
    simp [hi]


-- created on 2025-05-10
