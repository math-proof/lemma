import Lemma.Algebra.Ceil.eq.Neg.Floor
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Div.eq.One.of.Ne_0
import Lemma.Algebra.SubAdd.eq.Add_Sub
import Lemma.Algebra.EqSub.is.Eq_Add
import Lemma.Algebra.EqNegS.is.Eq
import Lemma.Algebra.Sub.eq.NegSub
import Lemma.Int.Add.eq.Sub_Neg
import Lemma.Algebra.EqAddS.of.Eq.Eq
import Lemma.Algebra.FloorAdd1.eq.Add1Floor
import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Int.FDivAdd.eq.Add1FDiv.of.Ne_0
import Lemma.Algebra.MulAdd.eq.AddMulS
import Lemma.Algebra.Sub.eq.Add_Neg
import Lemma.Int.AddFModS.eq.FModNegSign
import Lemma.Algebra.FModNegSign.eq.Sub_Sign
import Lemma.Algebra.SubNeg
import Lemma.Nat.Add
import Lemma.Int.Sub_Add.eq.SubSub
import Lemma.Algebra.EqSubS.is.Eq
import Lemma.Nat.Mul
import Lemma.Algebra.EqAddS.is.Eq
import Lemma.Algebra.AddMul.eq.MulAdd_1
import Lemma.Bool.Ne.is.NotEq
import Lemma.Algebra.Eq_0.of.Mul.eq.Zero.Ne_0
import Lemma.Int.Eq_Neg.of.Add.eq.Zero
import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Algebra.CoeNeg.eq.NegCoe
import Lemma.Algebra.DivNeg.eq.NegDiv
open Algebra Bool Int Nat


/--
This lemma establishes an equivalence between the ceiling of the division of two integers and the floor of an adjusted division expression.
Specifically, for integers `n` and `d`, the ceiling of `n / d` is equal to the floor of `(d + n - sign(d)) / d`.
This relationship leverages properties of the ceiling and floor functions, along with the sign of the divisor `d`, to transform the ceiling operation into a floor operation with a modified numerator.
The proof involves case analysis on whether `d` is zero and utilizes algebraic manipulations and properties of integer division to achieve the equivalence.
-/
@[main]
private lemma main
  {n d : ℤ} :
-- imply
  ⌈n / (d : ℚ)⌉ = ⌊(d + n - sign d) / (d : ℚ)⌋ := by
-- proof
  by_cases h : (d : ℚ) = 0
  ·
    rw [h]
    norm_num
  ·
    rw [Ceil.eq.Neg.Floor]
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
    rw [FDiv.eq.FloorDiv] at this
    rw [FDiv.eq.FloorDiv] at this
    rw [CoeNeg.eq.NegCoe] at this
    rw [DivNeg.eq.NegDiv] at this
    norm_cast at this


-- created on 2025-03-05
-- updated on 2025-04-04
