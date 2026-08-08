import Lemma.Hyperreal.NotInfiniteMul.of.NotInfinite.NotInfinite
import Lemma.Tensor.DataMul.eq.MulDataS
import Lemma.Tensor.NotInfiniteGetData
open Hyperreal Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.NotInfiniteGetDataMul |
| fin | Tensor.NotInfiniteGetDataMul.fin |
-/
@[main, fin]
private lemma main
-- given
  (A B : Tensor ℝ s)
  (i : Fin s.prod) :
-- imply
  ¬((A : Tensor ℝ* s) * (B : Tensor ℝ* s)).data[i] → ∞ := by
-- proof
  intro h
  rw [DataMul.eq.MulDataS (A := (A : Tensor ℝ* s)) (B := (B : Tensor ℝ* s))] at h
  simp only [GetElem.getElem, Vector.GetMul.eq.MulGetS.fin] at h
  exact absurd h (NotInfiniteMul.of.NotInfinite.NotInfinite (NotInfiniteGetData A i) (NotInfiniteGetData B i))


-- created on 2026-08-08
