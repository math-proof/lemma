import sympy.vector.vector
import Lemma.Algebra.Mul
import Lemma.Algebra.EqGetRange
open Algebra


@[main]
private lemma main
  [Mul α]
-- given
  (f g : Fin n → α) :
-- imply
  (List.Vector.range n).map f * (List.Vector.range n).map g = (List.Vector.range n).map (fun i => f i * g i) := by
-- proof
  ext i
  simp [HMul.hMul]
  simp [Mul.mul]
  rw [EqGetRange.fin]
  simp [HMul.hMul]


-- created on 2025-07-03
