import Lemma.Hyperreal.InfinitesimalMul.of.Infinitesimal.NotInfinite
import Lemma.Nat.Mul
open Hyperreal Nat


@[main]
private lemma main
  {a b : ℝ*}
-- given
  (h_a : ¬a → ∞)
  (h_b : b → 0) :
-- imply
  (a * b) → 0 := by
-- proof
  rw [Mul.comm]
  apply InfinitesimalMul.of.Infinitesimal.NotInfinite h_b h_a


-- created on 2025-12-20
