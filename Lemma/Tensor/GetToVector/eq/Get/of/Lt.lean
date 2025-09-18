import sympy.tensor.stack
import Lemma.Tensor.GetToVector.eq.Get
open Tensor


@[main]
private lemma main
  {v : Tensor α (n :: s)}
-- given
  (h : i < v.length) :
-- imply
  v.toVector[i] = v[i] := by
-- proof
  simp [Tensor.length] at h
  let i : Fin n := ⟨i, h⟩
  have := GetToVector.eq.Get v i
  simp_all
  assumption


-- created on 2025-05-27
