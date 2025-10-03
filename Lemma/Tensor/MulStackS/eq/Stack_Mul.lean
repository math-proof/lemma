import Mathlib.Data.Vector.MapLemmas
import sympy.tensor.stack
import Lemma.Algebra.Mul
import Lemma.Vector.MulFlattenS.eq.FlattenMul
import Lemma.Algebra.MulMapS.eq.Map_FunMul
open Algebra Vector


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
  simp
  rw [MulMapS.eq.Map_FunMul]


-- created on 2025-07-03
-- updated on 2025-09-24
