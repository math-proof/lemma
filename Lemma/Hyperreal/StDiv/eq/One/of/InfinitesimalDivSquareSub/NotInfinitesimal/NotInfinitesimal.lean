import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Rat.Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0
open Hyperreal Nat Rat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b)
  (h : ((1 + 2 * a * b) / (1 + a² + b²)).st = 1) :
-- imply
  st (a / b) = 1 := by
-- proof
  have h_a_ne_0 := Ne_0.of.NotInfinitesimal h_a
  have h_b_ne_0 := Ne_0.of.NotInfinitesimal h_b
  rw [Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0] at h
  have h_ab := Mul.ne.Zero.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0
  sorry


-- created on 2025-12-20
