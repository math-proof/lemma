import Lemma.Tensor.Unsqueeze.eq.TensorCast_Data
import Lemma.Tensor.EqData0'0
import Lemma.Tensor.EqDiv_0'0
import Lemma.Tensor.EqTensor0'0
import Lemma.Tensor.Sum.eq.Zero
import Lemma.Vector.ArraySlice0.eq.Zero
import Lemma.Vector.EqCast_0'0.of.Eq
import Lemma.Vector.Flatten0.eq.Zero
import Lemma.Vector.MapRange.eq.Zero
import Lemma.Vector.Repeat0.eq.Zero
import sympy.tensor.functions
open Tensor Vector


@[main]
private lemma main
  [ExpRing α]
-- given
  (X : Tensor α (0 :: s)) :
-- imply
  X.softmax 0 = 0 := by
-- proof
  simp [Tensor.softmax]
  rw [@Tensor.Sum.eq.Zero]
  unfold Tensor.keepdim
  simp
  rw [Unsqueeze.eq.TensorCast_Data]
  simp [EqData0'0]
  erw [EqCast_0'0.of.Eq]
  erw [EqTensor0'0]
  unfold Tensor.repeat
  simp [EqData0'0]
  unfold List.Vector.splitAt
  simp
  erw [EqCast_0'0.of.Eq]
  unfold List.Vector.unflatten
  simp only [ArraySlice0.eq.Zero]
  simp [EqCast_0'0.of.Eq]
  simp [Repeat0.eq.Zero]
  rw [MapRange.eq.Zero]
  rw [Flatten0.eq.Zero]
  simp [EqCast_0'0.of.Eq]
  erw [EqTensor0'0]
  apply @Tensor.EqDiv_0'0
  repeat simp [List.prod]


-- created on 2025-11-30
