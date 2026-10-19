import Lemma.Tensor.Dot.eq.SumMul__0
import Lemma.Vector.Dot.eq.SumMul
open Tensor Vector


@[path]
private lemma main
  [Mul α] [Add α] [Zero α]
-- given
  (A B : Tensor α [n]) :
-- imply
  A @ B = (A.data @ B.data : Tensor α []) := by
-- proof
  rw [Dot.eq.SumMul__0]
  apply Eq.of.EqDataS
  apply Eq.of.All_EqGetS.fin
  intro i
  fin_cases i
  repeat erw [Get_0.eq.Head.fin]
  simp [HeadDataSum.eq.SumData]
  rw [DataMul.eq.MulDataS]
  simp only [List.Vector.head]
  apply SumMul.eq.Dot


-- created on 2026-08-08
