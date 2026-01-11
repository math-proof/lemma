import stdlib.SEq
import sympy.tensor.Basic


@[main, fin]
private lemma main
-- given
  (h : s = s')
  (v : List.Vector (Tensor α s) n)
  (i : Fin n) :
-- imply
  (cast (congrArg (fun s => List.Vector (Tensor α s) n) h) v)[i] ≃ v[i] := by
-- proof
  subst h
  rfl


-- created on 2025-06-29
-- updated on 2025-07-04
