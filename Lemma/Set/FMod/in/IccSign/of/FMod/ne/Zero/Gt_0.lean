import Lemma.Algebra.FMod.ge.Zero.of.Gt_0
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.Ge_Add_1.of.Gt
import Lemma.Algebra.EqSign_1.of.Gt_0
import Lemma.Set.In_Icc.of.Le.Le
import Lemma.Algebra.FMod.eq.Sub_MulFDiv
import Lemma.Algebra.FDiv.eq.FloorDiv
import Lemma.Algebra.LeSub.is.Le_Add
import Lemma.Algebra.Add
import Lemma.Algebra.LeSub.is.Le_Add
import Lemma.Algebra.Le.of.LeDivS.Gt_0
import Lemma.Algebra.GtCoeS.is.Gt
import Lemma.Algebra.LeCoeS.is.Le
import Lemma.Algebra.CoeSub.eq.SubCoeS
import Lemma.Algebra.DivSub.eq.SubDivS
import Lemma.Algebra.Div.eq.One.of.Gt_0
import Lemma.Int.CoeMul.eq.MulCoeS
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Algebra.Ne.of.Gt
import Lemma.Set.In_IcoFloor
import Lemma.Set.Lt.of.In_Ico
open Algebra Set Int


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d > 0)
  (h₁ : n.fmod d ≠ 0) :
-- imply
  n.fmod d ∈ Icc (sign d) d := by
-- proof
  apply In_Icc.of.Le.Le
  ·
    have := FMod.ge.Zero.of.Gt_0 h₀ n
    have := Gt.of.Ge.Ne this h₁
    have := Ge_Add_1.of.Gt this
    simp at this
    have h_Eq := EqSign_1.of.Gt_0 h₀
    rwa [← h_Eq] at this
  ·
    rw [FMod.eq.Sub_MulFDiv]
    rw [FDiv.eq.FloorDiv]
    apply LeSub.of.Le_Add
    rw [Add.comm]
    apply Le_Add.of.LeSub
    have h₀ := GtCoeS.of.Gt.int (R := ℚ) h₀
    apply Le.of.LeCoeS.int (R := ℚ)
    apply Le.of.LeDivS.Gt_0 _ h₀
    rw [CoeSub.eq.SubCoeS.int]
    rw [DivSub.eq.SubDivS]
    rw [Div.eq.One.of.Gt_0 h₀]
    rw [CoeMul.eq.MulCoeS]
    have h_Ne := Ne.of.Gt h₀
    rw [EqDivMul.of.Ne_0 h_Ne]
    have := In_IcoFloor (x := (n : ℚ) / d)
    linarith [Lt.of.In_Ico this]


-- created on 2025-03-30
-- updated on 2025-05-04
