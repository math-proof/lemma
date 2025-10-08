import sympy.tensor.functions
import Lemma.Tensor.LengthExp.eq.Length
import Lemma.Tensor.GetMkMap.eq.MkMapDataGet
open Tensor


@[main]
private lemma fin
  [Exp α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  (exp X).get ⟨i, by simp [LengthExp.eq.Length]⟩ = exp (X.get i) := by
-- proof
  apply GetMkMap.eq.MkMapDataGet


@[main]
private lemma main
  [Exp α]
-- given
  (X : Tensor α s)
  (i : Fin X.length) :
-- imply
  have hi : i < (exp X).length := by simp [LengthExp.eq.Length]
  (exp X)[i] = exp X[i] := by
-- proof
  apply fin


-- created on 2025-10-08
