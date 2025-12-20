import Lemma.Rat.Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0
import Lemma.Hyperreal.Infinite.is.InfinitesimalInv
import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
open Hyperreal Rat


/--
similar with Hyperreal.StDiv.eq.One.of.StDiv_Add_Square.eq.One.Infinite.NotInfinitesimal.NotInfinitesimal
-/
@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b)
  (h_a_inf : ¬Infinite a)
  (h_a_inf : ¬Infinite b)
  (h : ((1 + 2 * a * b) / (1 + a² + b²)).st = 1) :
-- imply
  (a / b).st = 1 := by
-- proof
  have h_a_ne_0 := Ne_0.of.NotInfinitesimal h_a
  have h_b_ne_0 := Ne_0.of.NotInfinitesimal h_b
  rw [Div_Add_Square.eq.Div_AddInvMul.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0] at h
  sorry


-- created on 2025-12-20
