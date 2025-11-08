import Lemma.Int.FMod.le.Zero.of.Lt_0
import Lemma.Nat.Lt.of.Le.Ne
import Lemma.Nat.Le_Sub_1.of.Lt
import Lemma.Int.Sign.eq.Neg1.of.Lt_0
import Lemma.Set.In_Icc.of.Le.Le
import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.Le_Sub.is.LeAdd
import Lemma.Nat.Add
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Int.LeCoeS.is.Le
import Lemma.Rat.Le.of.GeDivS.Lt_0
import Lemma.Int.CoeSub.eq.SubCoeS
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.Div.eq.One.of.Lt_0
import Lemma.Int.CoeMul.eq.MulCoeS
import Lemma.Nat.Ne.of.Lt
import Lemma.Nat.EqDivMul.of.Ne_0
import Lemma.Set.Lt.of.In_Ico
import Lemma.Set.In_IcoFloor
open Set Int Nat Rat


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
    rw [FDiv.eq.FloorDiv (α := ℚ)]
    apply Le_Sub.of.LeAdd
    rw [Add.comm]
    apply LeAdd.of.Le_Sub
    have h₁ := LtCoeS.of.Lt (R := ℚ) h₁
    apply Le.of.LeCoeS (R := ℚ)
    apply Le.of.GeDivS.Lt_0 (h₁ := h₁)
    rw [CoeSub.eq.SubCoeS]
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
    rwa [← Sign.eq.Neg1.of.Lt_0 h₁] at this


-- created on 2025-03-30
-- updated on 2025-05-04
