import Lemma.Int.GeCoeS.is.Ge
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Set.Ge.of.In_Icc
import Lemma.Rat.Div.ge.Zero.of.Ge_0.Gt_0
import Lemma.Int.GtCoeS.is.Gt
import Lemma.Set.Le.of.In_Icc
import Lemma.Nat.Lt_Add_1.of.Le
import Lemma.Rat.LtDiv.of.Lt.Gt_0
open Set Int Nat Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h₀ : d > 0)
  (h₁ : n ∈ Icc 0 (d - 1)) :
-- imply
  n // d = 0 := by
-- proof
  rw [FDiv.eq.FloorDiv (α := ℚ)]
  rw [EqFloor.is.Le.Lt]
  constructor
  ·
    apply Div.ge.Zero.of.Ge_0.Gt_0
    have := Ge.of.In_Icc h₁
    exact GeCoeS.of.Ge this
    exact GtCoeS.of.Gt h₀
  ·
    norm_num
    apply LtDiv.of.Lt.Gt_0
    ·
      norm_num
      have := Le.of.In_Icc h₁
      have := Lt_Add_1.of.Le this
      simp at this
      assumption
    ·
      exact GtCoeS.of.Gt h₀


-- created on 2025-03-30
-- updated on 2025-04-26
