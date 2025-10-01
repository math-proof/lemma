import sympy.sets.sets
import Lemma.Set.Any_In.is.Ne_Empty
import Lemma.Algebra.Le.of.Le.Le
open Set Algebra


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : Icc a b ≠ ∅) :
-- imply
  a ≤ b := by
-- proof
  let ⟨e, h_e⟩ := Any_In.of.Ne_Empty h
  apply Le.of.Le.Le h_e.left h_e.right


-- created on 2025-10-01
