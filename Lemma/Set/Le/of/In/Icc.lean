import Lemma.Set.In_Iic.is.Le
import sympy.sets.sets
import sympy.Basic
open Set


@[path]
private lemma main
  [Preorder α]
  {n b : α}
-- given
  (h : n ≤ b) :
-- imply
  n ∈ Iic b := by
-- proof
  apply In_Iic.of.Le h


-- created on 2026-10-17
