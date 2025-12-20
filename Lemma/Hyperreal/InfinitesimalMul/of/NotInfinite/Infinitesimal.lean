import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Nat.Mul
open Hyperreal Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinite a)
  (h_b : Infinitesimal b) :
-- imply
  Infinitesimal (a * b) := by
-- proof
  rw [Mul.comm]
  apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_b h_a


-- created on 2025-12-20
