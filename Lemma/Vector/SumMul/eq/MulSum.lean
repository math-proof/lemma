import Lemma.Vector.Sum.eq.Sum_Get
import Lemma.Vector.GetMul.eq.MulGet
import Mathlib.Algebra.BigOperators.Ring.Finset
open Vector


@[path]
private lemma main
  [NonUnitalNonAssocSemiring α]
-- given
  (x : List.Vector α n)
  (a : α) :
-- imply
  (x * a).sum = x.sum * a := by
-- proof
  repeat rw [Sum.eq.Sum_Get]
  simp only [GetMul.eq.MulGet]
  rw [Finset.sum_mul]


-- created on 2025-09-24
-- updated on 2026-11-20
