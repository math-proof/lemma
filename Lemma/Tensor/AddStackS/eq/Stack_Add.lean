import Lemma.Tensor.Eq.is.EqDataS
import sympy.tensor.stack
import Lemma.Nat.Add
import Lemma.Vector.AddFlattenS.eq.FlattenAdd
import Lemma.Vector.AddMapS.eq.Map_FunAdd
open Vector Nat Tensor


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
  apply Eq.of.EqDataS
  simp [GetElem.getElem]
  let a := (List.Vector.range s₀).map fun x => (A.get x).data
  let b := (List.Vector.range s₀).map fun x => (B.get x).data
  show a.flatten + b.flatten = ((List.Vector.range s₀).map fun x => (A.get x).data + (B.get x).data).flatten
  rw [AddFlattenS.eq.FlattenAdd]
  congr
  exact AddMapS.eq.Map_FunAdd _ _


-- created on 2025-07-20
-- updated on 2025-09-24
