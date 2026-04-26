import stdlib.SEq
import sympy.tensor.Basic


@[main, fin]
private lemma main
-- given
  (h_s : s = s')
  (h_m : m = m')
  (v : List.Vector (Tensor α s) m)
  (i : Fin m) :
-- imply
  (cast (congrArg₂ (fun s => List.Vector (Tensor α s)) h_s h_m) v)[i] ≃ v[i] := by
-- proof
  subst h_s h_m
  rfl


-- created on 2026-04-26
