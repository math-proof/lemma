import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.Div.ge.Zero.of.Le_0.Lt_0
import Lemma.Set.Le.of.In_Icc
import Lemma.Int.LeCoeS.is.Le
import Lemma.Int.LtCoeS.is.Lt
import Lemma.Rat.LtDiv.of.Gt.Lt_0
import Lemma.Set.Ge.of.In_Icc
import Lemma.Nat.Lt.of.LeAdd_1
open Set Int Rat Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d < 0)
  (h₁ : n ∈ Icc (d + 1) 0) :
-- imply
  n // d = 0 := by
-- proof
  rw [FDiv.eq.FloorDiv]
  rw [EqFloor.is.Le.Lt]
  constructor
  ·
    apply Div.ge.Zero.of.Le_0.Lt_0
    ·
      have := Le.of.In_Icc h₁
      exact LeCoeS.of.Le this
    ·
      exact LtCoeS.of.Lt h₀
  ·
    norm_num
    apply LtDiv.of.Gt.Lt_0
    ·
      norm_num
      have := Ge.of.In_Icc h₁
      exact Gt.of.Ge_Add_1 this
    ·
      exact LtCoeS.of.Lt h₀


-- created on 2025-03-30
-- updated on 2025-04-26
