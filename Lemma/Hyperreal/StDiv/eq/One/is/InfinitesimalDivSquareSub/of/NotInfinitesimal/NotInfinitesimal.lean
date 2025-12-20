import Lemma.Hyperreal.EqSt.of.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub
import Lemma.Hyperreal.InfinitesimalSub.of.EqSt.NotInfinite
import Lemma.Hyperreal.NotInfiniteDiv_Add_Square.of.StDiv.eq.One
import Lemma.Hyperreal.StDiv_Add_Square.eq.One.of.StDiv.eq.One
import Lemma.Rat.DivSquareSub.eq.Sub1DivAddS
open Hyperreal Rat


@[main, comm, mp, mpr]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : ¬Infinitesimal b) :
-- imply
  st (a / b) = 1 ↔ ((a - b)² / (1 + a² + b²)).Infinitesimal := by
-- proof
  rw [DivSquareSub.eq.Sub1DivAddS]
  rw [InfinitesimalSub.comm]
  constructor <;>
    intro h
  ·
    apply InfinitesimalSub.of.EqSt.NotInfinite
    ·
      apply NotInfiniteDiv_Add_Square.of.StDiv.eq.One h
    ·
      apply StDiv_Add_Square.eq.One.of.StDiv.eq.One h
  ·
    have h := EqSt.of.InfinitesimalSub h
    sorry


-- created on 2025-12-20
