import sympy.sets.sets
import Lemma.Set.Any_In.is.Ne_Empty
import Lemma.Algebra.Lt.of.Lt.Lt
open Set Algebra


@[main]
private lemma main
  [Preorder α]
  {a b : α}
-- given
  (h : Ioo a b ≠ ∅) :
-- imply
  a < b := by
-- proof
  let ⟨e, h_e⟩ := Any_In.of.Ne_Empty h
  apply Lt.of.Lt.Lt h_e.left h_e.right


-- created on 2025-10-01
