import Lemma.Hyperreal.InfiniteMul.of.Infinite.NotInfinitesimal
import Lemma.Nat.Mul
open Nat Hyperreal


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬Infinitesimal a)
  (h_b : Infinite b) :
-- imply
  Infinite (a * b) := by
-- proof
  rw [Mul.comm]
  apply InfiniteMul.of.Infinite.NotInfinitesimal h_b h_a


-- created on 2025-12-20
