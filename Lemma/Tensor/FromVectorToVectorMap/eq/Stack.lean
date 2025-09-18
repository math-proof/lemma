import sympy.tensor.stack
import Lemma.Algebra.EqGetRange
open Algebra


@[main]
private lemma main
-- given
  (g : List ℕ → List ℕ)
  (f : Tensor α s → Tensor α (g s))
  (X : Tensor α (n :: s)) :
-- imply
  Tensor.fromVector (X.toVector.map f) = [i < n] (f X[i]) := by
-- proof
  unfold Stack
  congr
  ext i
  simp [EqGetRange.fin]
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]


-- created on 2025-07-13
