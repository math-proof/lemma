import Lemma.Algebra.FMod.le.Zero.of.Lt_0
import Lemma.Algebra.Lt.of.Le.Ne
import Lemma.Algebra.Le_Sub_1.of.Lt
import Lemma.Algebra.Sign.eq.Neg1.of.Lt_0
import Lemma.Set.In_Icc.of.Le.Le
import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Algebra.Le_Sub.is.LeAdd
import Lemma.Algebra.Add
import Lemma.Algebra.LtCoeS.is.Lt
import Lemma.Algebra.LeCoeS.is.Le
import Lemma.Algebra.Le.of.GeDivS.Lt_0
import Lemma.Algebra.CoeSub.eq.SubCoeS
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Algebra.Div.eq.One.of.Lt_0
import Lemma.Algebra.CoeMul.eq.MulCoeS
import Lemma.Algebra.Ne.of.Lt
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Set.Lt.of.In_Ico
import Lemma.Set.In_IcoFloor
open Algebra Set


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : n.fmod d ≠ 0)
  (h₁ : d < 0) :
-- imply
  n.fmod d ∈ Icc d (sign d) := by
-- proof
  apply In_Icc.of.Le.Le
  ·
    rw [FMod.eq.Sub_MulFDiv]
    rw [FDiv.eq.FloorDiv]
    apply Le_Sub.of.LeAdd
    rw [Add.comm]
    apply LeAdd.of.Le_Sub
    have h₁ := LtCoeS.of.Lt.int (R := ℚ) h₁
    apply Le.of.LeCoeS.int (R := ℚ)
    apply Le.of.GeDivS.Lt_0 (h₁ := h₁)
    rw [CoeSub.eq.SubCoeS.int]
    rw [DivSub.eq.SubDivS]
    rw [Div.eq.One.of.Lt_0 h₁]
    rw [CoeMul.eq.MulCoeS]
    have h_Ne := Ne.of.Lt h₁
    rw [EqDivMul.of.Ne_0 h_Ne]
    have := In_IcoFloor (x := (n : ℚ) / d)
    have := Lt.of.In_Ico this
    linarith
  ·
    have := FMod.le.Zero.of.Lt_0 h₁ n
    have := Lt.of.Le.Ne h₀ this
    have := Le_Sub_1.of.Lt this
    simp at this
    rw [← Sign.eq.Neg1.of.Lt_0 h₁] at this
    assumption


-- created on 2025-03-30
-- updated on 2025-05-04
