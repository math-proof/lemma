import Lemma.Int.Ceil.eq.NegFloorNeg
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Int.EqSub.is.Eq_Add
import Lemma.Int.EqNegS.is.Eq
import Lemma.Int.Sub.eq.NegSub
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Nat.EqAddS.of.Eq.Eq
import Lemma.Rat.FloorAdd1.eq.Add1Floor
import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.FDivAdd.eq.Add1FDiv.of.Ne_0
import Lemma.Nat.MulAdd.eq.AddMulS
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Int.AddFModS.eq.FModNegSign
import Lemma.Int.FModNegSign.eq.Sub_Sign
import Lemma.Int.SubNeg
import Lemma.Nat.Add
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Int.EqSubS.is.Eq
import Lemma.Nat.Mul
import Lemma.Nat.EqAddS.is.Eq
import Lemma.Nat.AddMul.eq.MulAdd_1
import Lemma.Bool.Ne.is.NotEq
import Lemma.Int.Eq_0.of.Mul.eq.Zero.Ne_0
import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.CoeNeg.eq.NegCoe
import Lemma.Rat.DivNeg.eq.NegDiv
open Bool Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α] [FloorRing α]
  {n d : ℤ} :
-- imply
  ⌈n / (d : α)⌉ = ⌊(d + n - sign d) / (d : α)⌋ := by
-- proof
  if h : (d : α) = 0 then
    rw [h]
    norm_num
  else
    rw [Ceil.eq.NegFloorNeg]
    rw [DivSub.eq.SubDivS]
    rw [DivAdd.eq.AddDivS]
    rw [Div.eq.One.of.Ne_0 h]
    rw [SubAdd.eq.Add_Sub]
    rw [← DivSub.eq.SubDivS]
    norm_cast
    rw [FloorAdd1.eq.Add1Floor]
    apply Eq_Add.of.EqSub
    apply Eq.of.EqNegS
    rw [NegSub.eq.Sub]
    rw [Sub_Neg.eq.Add]
    have h₀ := FMod.eq.Sub_MulFDiv (n := -n) (d := d)
    have h₁ := FMod.eq.Sub_MulFDiv (n := (d + n - sign (d))) (d := d)
    rw [SubAdd.eq.Add_Sub] at h₁
    norm_cast at h
    have h := Ne.of.NotEq h
    rw [FDivAdd.eq.Add1FDiv.of.Ne_0 h] at h₁
    rw [MulAdd.eq.AddMulS] at h₁
    norm_num at h₁
    have := EqAddS.of.Eq.Eq h₀ h₁
    ring_nf at this
    rw [Add_Sub.eq.SubAdd] at this
    rw [Add_Neg.eq.Sub] at this
    rw [AddFModS.eq.FModNegSign] at this
    rw [FModNegSign.eq.Sub_Sign] at this
    rw [SubNeg.comm] at this
    rw [SubSub.eq.Sub_Add] at this
    rw [Add.comm] at this
    rw [Sub_Add.eq.SubSub] at this
    have := Eq.of.EqSubS this
    rw [Mul.comm (a := d)] at this
    have := EqNegS.of.Eq this
    rw [NegSub.eq.Sub] at this
    rw [Sub_Neg.eq.Add] at this
    rw [← MulAdd.eq.AddMulS] at this
    have := EqAddS.of.Eq d this
    simp at this
    have := this.symm
    rw [AddMul.eq.MulAdd_1] at this
    have := Eq_0.of.Mul.eq.Zero.Ne_0 this h
    have := Eq_Neg.of.Add.eq.Zero this
    repeat rw [FDiv.eq.FloorDiv (α := α)] at this
    rw [CoeNeg.eq.NegCoe] at this
    rw [DivNeg.eq.NegDiv] at this
    norm_cast at this


-- created on 2025-03-05
-- updated on 2025-04-04
