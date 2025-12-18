import Lemma.Nat.Gt.is.Ge.Ne
import Lemma.Hyperreal.NeSt_0.is.NotInfinite.NotInfinitesimal
import Lemma.Hyperreal.GeSt_0.of.Ge_0
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h₀ : ¬x.Infinitesimal)
  (h₁ : ¬x.Infinite)
  (h_x : x > 0) :
-- imply
  st x > 0 := by
-- proof
  apply Gt.of.Ge.Ne
  .
    apply GeSt_0.of.Ge_0 (by linarith) (x := x)
  .
    apply NeSt_0.of.NotInfinite.NotInfinitesimal h₁ h₀


-- created on 2025-12-18
