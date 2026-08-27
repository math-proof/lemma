import sympy.tensor.stack
import Lemma.Vector.EqGetRange
import Lemma.Vector.GetMap.eq.UFnGet
open Vector


@[main]
private lemma main
-- given
  (g : List ℕ → List ℕ)
  (f : Tensor α s → Tensor α (g s))
  (X : Tensor α (n :: s)) :
-- imply
  Tensor.OfVector (X.toVector.map f) = [i < n] (f X[i]) := by
-- proof
  unfold Stack
  congr
  ext i
  erw [GetMap.eq.UFnGet]
  erw [GetMap.eq.UFnGet]
  erw [EqGetRange.fin]
  simp [GetElem.getElem]
  simp [Tensor.get]
  simp [GetElem.getElem]
  rfl


-- created on 2025-07-13
