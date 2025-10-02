import sympy.vector.vector
import Lemma.Algebra.Ge.of.NotLt
import Lemma.Algebra.GetElem!.eq.None.of.Ge_Length
open Algebra


@[main]
private lemma main
-- given
  (v : List α)
  (a : α)
  (i : ℕ) :
-- imply
  v[i]? = some a ↔ ∃ h : i < v.length, v[i] = a := by
-- proof
  by_cases hi : i < v.length <;>
    simp [hi]


-- created on 2025-05-10
