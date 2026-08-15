import Lemma.Tensor.MapGetSlice.eq.GetSliceMap
import sympy.tensor.functions
open Tensor


@[main, comm]
private lemma main
  [Exp α]
-- given
  (X : Tensor α (n :: s))
  (slice : Slice) :
-- imply
  exp (X.getSlice slice) = (exp X).getSlice slice := by
-- proof
  change (X.getSlice slice).map Exp.exp = (X.map Exp.exp).getSlice slice
  rw [MapGetSlice.eq.GetSliceMap]


-- created on 2026-08-14
-- updated on 2026-08-15
