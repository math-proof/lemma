import Lemma.Algebra.Any_Eq_Mul.of.FMod.eq.Zero
import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Nat.Add
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Int.CoeAdd.eq.AddCoeS
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Int.CoeMul.eq.MulCoeS
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Bool.Ne.is.NotEq
import Lemma.Algebra.NeCoeS.of.Ne
import Lemma.Int.FloorAdd.eq.AddFloor
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.Sub_Add.eq.SubSub
import Lemma.Algebra.SubSub.eq.Neg
open Algebra Bool Int Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d = 0)
  (m : ℤ) :
-- imply
  (n + m).fmod d = m.fmod d := by
-- proof
  by_cases h_d : d = 0
  ·
    rw [h_d]
    norm_num
    rw [h_d] at h
    norm_num at h
    assumption
  ·
    have h_d := Ne.of.NotEq h_d
    have := Any_Eq_Mul.of.FMod.eq.Zero h
    let ⟨k, h_n⟩ := this
    rw [h_n]
    rw [FMod.eq.Sub_MulFDiv]
    rw [FMod.eq.Sub_MulFDiv]
    rw [Add.comm]
    rw [SubAdd.eq.Add_Sub]
    rw [Sub.eq.Add_Neg (a := m)]
    apply EqAddS.of.Eq.left
    rw [FDiv.eq.FloorDiv]
    rw [CoeAdd.eq.AddCoeS]
    rw [DivAdd.eq.AddDivS]
    rw [CoeMul.eq.MulCoeS]
    have := NeCoeS.of.Ne (R := ℚ) h_d
    rw [EqDivMul.of.Ne_0 this]
    rw [FloorAdd.eq.AddFloor]
    rw [MulAdd.eq.AddMulS]
    rw [Sub_Add.eq.SubSub]
    rw [SubSub.eq.Neg]
    rw [FDiv.eq.FloorDiv]


-- created on 2025-03-30
-- updated on 2025-04-26
