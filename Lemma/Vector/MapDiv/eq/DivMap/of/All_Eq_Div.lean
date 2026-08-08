import Lemma.Vector.GetDiv.eq.DivGet
import sympy.vector.vector
open Vector Nat


@[main, comm]
private lemma main
  [Div α]
  [Div β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a / b) = f a / f b)
  (a : List.Vector α n)
  (b : α) :
-- imply
  (a / b).map f = a.map f / f b := by
-- proof
  ext k
  simp [GetDiv.eq.DivGet.fin]
  apply hf


-- created on 2026-08-08
