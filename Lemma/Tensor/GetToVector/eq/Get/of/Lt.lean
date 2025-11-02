import sympy.tensor.stack
import Lemma.Tensor.GetToVector.eq.Get
open Tensor


@[main]
private lemma main
  {X : Tensor α (n :: s)}
-- given
  (h : i < X.length) :
-- imply
  X.toVector[i] = X[i] := by
-- proof
  simp [Tensor.length] at h
  let i : Fin n := ⟨i, h⟩
  have := GetToVector.eq.Get.cons X i
  simp_all
  assumption


-- created on 2025-05-27
