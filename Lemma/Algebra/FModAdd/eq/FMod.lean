import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.Add
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Algebra.CoeAdd.eq.AddCoeS
import Lemma.Algebra.DivAdd.eq.Add1Div
import Lemma.Algebra.NeCoeS.of.Ne
import Lemma.Algebra.FloorAdd1.eq.Add1Floor
import Lemma.Algebra.MulAdd.eq.AddMulS
open Algebra


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (d + n).fmod d = n.fmod d := by
-- proof
  by_cases h : d = 0
  ·
    rw [h]
    norm_num
  rw [FMod.eq.Sub_MulFDiv]
  rw [FMod.eq.Sub_MulFDiv]
  rw [Add.comm]
  rw [SubAdd.eq.Add_Sub]
  rw [Sub.eq.Add_Neg (a := n)]
  apply EqAddS.of.Eq.left
  rw [FDiv.eq.FloorDiv]
  rw [FDiv.eq.FloorDiv]
  rw [CoeAdd.eq.AddCoeS.int]
  rw [Add.comm]
  have h := NeCoeS.of.Ne (R := ℚ) h
  rw [DivAdd.eq.Add1Div h]
  rw [FloorAdd1.eq.Add1Floor]
  rw [MulAdd.eq.AddMulS]
  norm_num


-- created on 2025-03-29
-- updated on 2025-04-26
