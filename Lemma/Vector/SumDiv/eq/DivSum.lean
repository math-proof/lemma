import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.GetDiv.eq.DivGet
import Mathlib.Algebra.BigOperators.Ring.Finset
open Vector


@[path]
private lemma main
  [DivisionSemiring α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  (x / a).sum = x.sum / a := by
-- proof
  repeat rw [Sum.eq.Sum_Get]
  simp only [GetDiv.eq.DivGet]
  simp only [div_eq_mul_inv]
  rw [Finset.sum_mul]


-- created on 2025-09-22
-- updated on 2026-11-20
