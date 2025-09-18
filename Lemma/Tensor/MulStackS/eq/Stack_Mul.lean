import sympy.tensor.stack
import Lemma.Algebra.Mul
import Lemma.Algebra.MulFlattenS.eq.FlattenMul
import Lemma.Algebra.MapMap.eq.Map_Comp
import Lemma.Algebra.MulMapS.eq.Map_FunMul
open Algebra


@[main]
private lemma main
  [Mul α]
-- given
  (A B : Tensor α (s₀ :: s)) :
-- imply
  ([i < s₀] A[i]) * [i < s₀] B[i] = [i < s₀] A[i] * B[i] := by
-- proof
  unfold Stack Tensor.fromVector
  simp only [HMul.hMul]
  simp only [Mul.mul]
  rw [MulFlattenS.eq.FlattenMul]
  simp [MapMap.eq.Map_Comp.vector]
  rw [MulMapS.eq.Map_FunMul]


-- created on 2025-07-03
