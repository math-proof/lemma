import Lemma.Tensor.Lt.is.LtDataS
import Lemma.Tensor.Sum.eq.MkListSumData
import Lemma.Tensor.EqData0'0
import Lemma.Vector.Lt.is.All_Lt
open Tensor Vector


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.GtSumData_0.is.GtSum_0 |
| comm | Tensor.GtSum_0.is.GtSumData_0 |
| mp | Tensor.GtSum_0.of.GtSumData_0 |
| mpr | Tensor.GtSumData_0.of.GtSum_0 |
-/
@[main, comm, mp, mpr]
private lemma main
  [Add α] [Zero α]
  [LT α]
-- given
  (X : Tensor α [n]) :
-- imply
  X.data.sum > 0 ↔ X.sum > 0 := by
-- proof
  rw [Sum.eq.MkListSumData (X := X)]
  constructor
  · intro h
    rw [gt_iff_lt, Lt.is.LtDataS, Lt.is.All_Lt]
    intro i
    fin_cases i
    simpa [GetElem.getElem, EqData0'0]
  · intro h
    rw [gt_iff_lt, Lt.is.LtDataS, Lt.is.All_Lt] at h
    have := h ⟨0, by simp⟩
    rwa [GetElem.getElem, EqData0'0] at this


-- created on 2026-07-29
