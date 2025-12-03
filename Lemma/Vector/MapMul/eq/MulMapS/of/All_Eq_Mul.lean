import Lemma.Nat.Mul
import Lemma.Vector.GetMul.eq.MulGetS
import sympy.vector.vector
open Nat Vector


@[main, comm]
private lemma main
  [Mul α]
  [Mul β]
  {f : α → β}
-- given
  (hf : ∀ a b, f (a * b) = f a * f b)
  (a b : List.Vector α n) :
-- imply
  (a * b).map f = a.map f * b.map f := by
-- proof
  ext k
  simp [GetMul.eq.MulGetS.fin]
  apply hf


-- created on 2025-12-03
