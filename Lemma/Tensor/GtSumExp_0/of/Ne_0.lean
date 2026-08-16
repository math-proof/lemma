import Lemma.Tensor.DataExp.eq.ExpData
import Lemma.Tensor.GtSumData_0.is.GtSum_0
import Lemma.Vector.GtSumExp_0
open Tensor Vector


@[main]
private lemma main
  [ExpPos α]
  [IsOrderedCancelAddMonoid α]
  {X : Tensor α [n]}
-- given
  (h : n ≠ 0) :
-- imply
  (exp X).sum > 0 := by
-- proof
  have : NeZero n := ⟨h⟩
  have : NeZero [n].prod := ⟨by simpa using h⟩
  apply GtSum_0.of.GtSumData_0
  rw [DataExp.eq.ExpData]
  apply Vector.GtSumExp_0


-- created on 2026-08-16
