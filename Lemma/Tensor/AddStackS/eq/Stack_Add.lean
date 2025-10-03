import sympy.tensor.stack
import Mathlib.Data.Vector.MapLemmas
import Lemma.Algebra.Add
import Lemma.Vector.AddFlattenS.eq.FlattenAdd
import Lemma.Algebra.AddMapS.eq.Map_FunAdd
open Algebra Vector


@[main]
private lemma main
  [Add α]
-- given
  (A B : Tensor α (s₀ :: s)) :
-- imply
  ([i < s₀] A[i]) + [i < s₀] B[i] = [i < s₀] (A[i] + B[i]) := by
-- proof
  unfold Stack Tensor.fromVector
  simp only [HAdd.hAdd]
  simp only [Add.add]
  rw [AddFlattenS.eq.FlattenAdd]
  simp
  rw [AddMapS.eq.Map_FunAdd]


-- created on 2025-07-20
-- updated on 2025-09-24
