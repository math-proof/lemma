import Instance.Data.Vector.Basic.Dot
import Lemma.Vector.Dot.eq.SumMul
open Nat Vector


@[path]
private lemma Comm
  [CommMagma α] [AddCommMonoid α]
-- given
  (a b : List.Vector α n) :
-- imply
  a ⬝ᵥ b = b ⬝ᵥ a := by
-- proof
  rw [Dot.eq.SumMul, Dot.eq.SumMul, Mul.comm]


-- created on 2026-07-29
