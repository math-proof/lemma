import Lemma.Nat.Lt.is.Le.Ne
import Lemma.Hyperreal.LeSt_0.of.Le_0
import Lemma.Hyperreal.NeSt_0.is.NotInfinite.NotInfinitesimal
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (h₀ : ¬x.Infinitesimal)
  (h₁ : ¬x.Infinite)
  (h_x : x < 0) :
-- imply
  st x < 0 := by
-- proof
  apply Lt.of.Le.Ne
  ·
    apply LeSt_0.of.Le_0 (by linarith) (x := x)
  ·
    apply NeSt_0.of.NotInfinite.NotInfinitesimal h₁ h₀


-- created on 2025-12-18
