import sympy.vector.vector
import Lemma.Algebra.Sum.eq.SumFinLength_Get
open Algebra


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (v : List.Vector α n) :
-- imply
  v.sum = ∑ i : Fin n, v[i] := by
-- proof
  obtain ⟨v, h⟩ := v
  unfold List.Vector.sum
  simp
  rw [Sum.eq.SumFinLength_Get v]
  congr
  aesop


-- created on 2025-07-14
