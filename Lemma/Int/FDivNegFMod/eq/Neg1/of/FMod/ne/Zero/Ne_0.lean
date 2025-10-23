import sympy.core.relational
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.EqFloor.is.Le.Lt
import Lemma.Rat.DivNeg.eq.NegDiv
import Lemma.Algebra.DivInt.eq.Div
import Lemma.Algebra.CoeNeg.eq.NegCoe
import Lemma.Algebra.LeNegS.of.Ge
import Lemma.Int.DivFMod.lt.One
import Lemma.Int.LtNeg_0.of.Gt_0
import Lemma.Int.DivFMod.ge.Zero
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.Div.ne.Zero.of.Ne_0.Ne_0
import Lemma.Int.NeCoeS.of.Ne
import Lemma.Bool.Ne.is.NotEq
open Algebra Bool Int Rat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : n.fmod d ≠ 0)
  (h_d : d ≠ 0) :
-- imply
  (-(n.fmod d)) // d = -1 := by
-- proof
  denote h_r : r = n.fmod d
  rw [← h_r]
  rw [FDiv.eq.FloorDiv]
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
    have := DivFMod.lt.One (n := n) (d := d)
    rw [← h_r] at this
    linarith
  ·
    norm_cast
    simp
    rw [DivInt.eq.Div]
    rw [CoeNeg.eq.NegCoe]
    rw [DivNeg.eq.NegDiv]
    apply LtNeg_0.of.Gt_0
    have := DivFMod.ge.Zero (n := n) (d := d)
    rw [← h_r] at this
    apply Gt.of.Ge.Ne this
    rw [← h_r] at h
    apply Div.ne.Zero.of.Ne_0.Ne_0
    exact NeCoeS.of.Ne h
    have := Ne.of.NotEq h_d
    exact NeCoeS.of.Ne this


-- created on 2025-03-30
