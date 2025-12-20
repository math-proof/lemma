import Lemma.Hyperreal.Ne_0.of.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.InvStInv
import Lemma.Hyperreal.StDiv.eq.One.of.StDiv_Add_Square.eq.One.Infinite.NotInfinitesimal.NotInfinitesimal
import Lemma.Hyperreal.StDiv.eq.One.of.StDiv_Add_Square.eq.One.NotInfinite.NotInfinite.NotInfinitesimal.NotInfinitesimal
import Lemma.Nat.AddAdd
import Lemma.Nat.Mul.ne.Zero.of.Ne_0.Ne_0
import Lemma.Nat.MulMul
open Hyperreal Nat


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
  have h_ab := Mul.ne.Zero.of.Ne_0.Ne_0 h_a_ne_0 h_b_ne_0
  if h_a_inf : a.Infinite then
    apply StDiv.eq.One.of.StDiv_Add_Square.eq.One.Infinite.NotInfinitesimal.NotInfinitesimal h_a h_b h_a_inf h
  else if h_b_inf : b.Infinite then
    rw [MulMul.comm] at h
    rw [AddAdd.comm] at h
    have := StDiv.eq.One.of.StDiv_Add_Square.eq.One.Infinite.NotInfinitesimal.NotInfinitesimal h_b h_a h_b_inf h
    rw [StDiv.eq.InvStInv] at this
    simp at this
    assumption
  else
    apply StDiv.eq.One.of.StDiv_Add_Square.eq.One.NotInfinite.NotInfinite.NotInfinitesimal.NotInfinitesimal h_a h_b h_a_inf h_b_inf h


-- created on 2025-12-20
