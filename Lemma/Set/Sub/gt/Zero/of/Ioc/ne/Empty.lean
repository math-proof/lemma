import sympy.sets.sets
import Lemma.Algebra.Lt.of.Lt.Le
import Lemma.Algebra.Sub.gt.Zero.is.Lt
import Lemma.Set.Any_In.is.Ne_Empty
open Algebra Set


@[main]
private lemma main
  [AddGroup α] [Preorder α] [AddRightStrictMono α]
  {a b : α}
-- given
  (h : Ioc a b ≠ ∅) :
-- imply
  b - a > 0 := by
-- proof
  obtain ⟨x, hx⟩ := Any_In.of.Ne_Empty h
  have hab := Lt.of.Lt.Le hx.1 hx.2
  apply Sub.gt.Zero.of.Lt hab


-- created on 2025-10-01
