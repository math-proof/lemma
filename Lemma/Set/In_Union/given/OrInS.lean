import Lemma.Set.In_Union.is.OrInS
import sympy.Basic
open Set


@[main]
private lemma main
  {A B : Set α}
  {e : α}
-- given
  (h : e ∈ A ∨ e ∈ B) :
-- imply
  e ∈ A ∪ B := by
-- proof
  exact In_Union.of.OrInS h


-- created on 2026-10-03
