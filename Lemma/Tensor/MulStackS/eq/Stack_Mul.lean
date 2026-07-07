import Lemma.Tensor.Eq.is.EqDataS
import sympy.tensor.stack
import Lemma.Nat.Mul
import Lemma.Vector.FlattenMul.eq.MulFlattenS
import Lemma.Vector.MulMapS.eq.Map_FunMul
open Vector Nat Tensor


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
  apply Eq.of.EqDataS
  simp [GetElem.getElem]
  let a := (List.Vector.range s₀).map fun x => (A.get x).data
  let b := (List.Vector.range s₀).map fun x => (B.get x).data
  show a.flatten * b.flatten = ((List.Vector.range s₀).map fun x => (A.get x).data * (B.get x).data).flatten
  rw [← FlattenMul.eq.MulFlattenS]
  congr
  exact MulMapS.eq.Map_FunMul _ _


-- created on 2025-07-03
-- updated on 2025-09-24
