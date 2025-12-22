import Lemma.Hyperreal.Gt_0.of.Gt_0.InfinitesimalDivSquareSub.Infinite.Infinite
import Lemma.Hyperreal.Infinite.is.InfiniteNeg
import Lemma.Hyperreal.Ne_0.of.Infinite
import Lemma.Int.GtNeg_0.of.Lt_0
import Lemma.Int.Lt0Mul.of.Lt_0.Lt_0
import Lemma.Nat.Lt0Mul.of.Gt_0.Gt_0
import Lemma.Nat.Sub.eq.AddNeg
import sympy.core.power
open Hyperreal Int Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : a.Infinite)
  (h_b : b.Infinite)
  (h : Infinitesimal ((a - b)² / (a² + b² + 1))) :
-- imply
  a * b > 0 := by
-- proof
  if h_a_0 : a > 0 then
    apply Lt0Mul.of.Gt_0.Gt_0 h_a_0
    apply Gt_0.of.Gt_0.InfinitesimalDivSquareSub.Infinite.Infinite h_a h_b h h_a_0
  else if h_a_0 : a < 0 then
    apply Lt0Mul.of.Lt_0.Lt_0 h_a_0
    have h_a_0 := GtNeg_0.of.Lt_0 h_a_0
    have h_a := InfiniteNeg.of.Infinite h_a
    have h_b := InfiniteNeg.of.Infinite h_b
    have h : ((-a - -b)² / ((-a)² + (-b)² + 1)).Infinitesimal := by
      simp [AddNeg.eq.Sub]
      rwa [SquareSub.comm]
    have h_b_0 := Gt_0.of.Gt_0.InfinitesimalDivSquareSub.Infinite.Infinite h_a h_b h h_a_0
    simp at h_b_0
    assumption
  else
    have : a = 0 := by linarith
    have h_a_ne_0 := Ne_0.of.Infinite h_a
    contradiction


-- created on 2025-12-21
-- updated on 2025-12-22
