import Lemma.Hyperreal.StMul.eq.MulSt.of.NotInfinite
import Lemma.Nat.Mul
open Hyperreal Nat


@[main]
private lemma main
  {x : ℝ*}
-- given
  (r : ℝ)
  (h : ¬x → ∞) :
-- imply
  stdPart (r * x) = r * stdPart x := by
-- proof
  rw [Mul.comm]
  rw [StMul.eq.MulSt.of.NotInfinite h]
  rw [Mul.comm]


-- created on 2025-12-17
