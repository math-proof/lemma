import Lemma.Vector.GetDiv.eq.DivGetS
import sympy.vector.vector
open Vector


@[main, comm]
private lemma main
  [Div α]
  [Div β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a / b) = f a / f b)
  (a b : List.Vector α n) :
-- imply
  (a / b).map f = a.map f / b.map f := by
-- proof
  ext k
  simp [GetDiv.eq.DivGetS.fin]
  apply hf


-- created on 2026-08-08
