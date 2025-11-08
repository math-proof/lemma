import sympy.core.relational
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.DivNeg.eq.NegDiv
import Lemma.Int.DivInt.eq.Div
import Lemma.Int.CoeNeg.eq.NegCoe
import Lemma.Int.LeNegS.of.Ge
import Lemma.Int.DivFMod.lt.One
import Lemma.Int.LtNeg_0.of.Gt_0
import Lemma.Int.DivFMod.ge.Zero
import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Rat.Div.ne.Zero.of.Ne_0.Ne_0
import Lemma.Int.NeCoeS.of.Ne
import Lemma.Bool.Ne.is.NotEq
open Bool Int Rat Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d ≠ 0)
  (h_d : d ≠ 0) :
-- imply
  (-(n.fmod d)) // d = -1 := by
-- proof
  denote h_r : n.fmod d = r
  rw [h_r]
  rw [FDiv.eq.FloorDiv (α := ℚ)]
  norm_cast
  simp
  rw [EqFloor.is.Le.Lt]
  constructor
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    rw [CoeNeg.eq.NegCoe]
    rw [DivNeg.eq.NegDiv]
    apply LeNegS.of.Ge
    have := DivFMod.lt.One n d (α := ℚ)
    rw [h_r] at this
    linarith
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    rw [CoeNeg.eq.NegCoe]
    rw [DivNeg.eq.NegDiv]
    apply LtNeg_0.of.Gt_0
    have := DivFMod.ge.Zero n d (α := ℚ)
    rw [h_r] at this
    apply Gt.of.Ge.Ne this
    rw [h_r] at h
    apply Div.ne.Zero.of.Ne_0.Ne_0
    exact NeCoeS.of.Ne h
    have := Ne.of.NotEq h_d
    exact NeCoeS.of.Ne this


-- created on 2025-03-30
