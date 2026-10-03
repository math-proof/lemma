import Lemma.Set.In_Ico.is.Le.Lt
import sympy.Basic
open Set


@[main]
private lemma main
  [Preorder α]
  {a b x : α}
-- given
  (h : a ≤ x ∧ x < b) :
-- imply
  x ∈ Ico a b := by
-- proof
  exact In_Ico.of.Le.Lt h.1 h.2


-- created on 2026-10-03
