import Lemma.Vector.MapGetSlice.eq.GetSliceMap
import sympy.vector.functions
open Vector


@[main]
private lemma main
  [Exp α]
-- given
  (x : List.Vector α n)
  (s : Slice) :
-- imply
  exp (x.getSlice s) = (exp x).getSlice s := by
-- proof
  simp [Exp.exp]
  rw [MapGetSlice.eq.GetSliceMap]


-- created on 2026-08-14
-- updated on 2026-08-15
