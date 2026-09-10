import Lemma.Fin.Sum.of.All_Eq
import Lemma.Tensor.DataAppend.as.AppendDataS
import Lemma.Tensor.Dot.eq.TensorDotDataS
import Lemma.Tensor.DotHstack.eq.AddDotS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Vector.Dot.eq.SumMul
import Lemma.Vector.DotAppendS.eq.AddDotS
import Lemma.Vector.Eq.is.All_EqGetS
import Lemma.Vector.SEqMulS.of.SEq.SEq
import Lemma.Vector.Sum.of.SEq
open Tensor Vector


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A C : Tensor α [n])
  (B D : Tensor α [m]) :
-- imply
  (A ++ B) @ (C ++ D) = id (α := Tensor α []) (A @ C) + id (α := Tensor α []) (B @ D) := by
-- proof
  simp only [id]
  rw [Dot.eq.TensorDotDataS]
  rw [Dot.eq.TensorDotDataS A C]
  rw [Dot.eq.TensorDotDataS B D]
  apply Eq.of.EqDataS
  apply Vector.Eq.of.All_EqGetS.fin
  intro i
  fin_cases i
  simp [List.Vector.get]
  change (A ++ B).data @ (C ++ D).data = A.data @ C.data + B.data @ D.data
  rw [AddDotS.eq.DotAppendS A.data C.data B.data D.data]
  rw [Vector.Dot.eq.SumMul]
  rw [Vector.Dot.eq.SumMul (A.data ++ B.data) (C.data ++ D.data)]
  apply Sum.of.SEq
  exact SEqMulS.of.SEq.SEq (DataAppend.as.AppendDataS A B) (DataAppend.as.AppendDataS C D)


/--
Vector–matrix product of two row-block appends.
-/
@[main]
private lemma vm
  [Mul α] [AddCommMonoid α]
-- given
  (x : Tensor α [n])
  (y : Tensor α [m])
  (P : Tensor α [n, k])
  (Q : Tensor α [m, k]) :
-- imply
  (x ++ y) @ (P ++ Q) = id (α := Tensor α [k]) (x @ P) + id (α := Tensor α [k]) (y @ Q) := by
-- proof
  apply @Tensor.Eq.of.All_EqGetS.fin
  intro j
  trans (id (α := Tensor α [k]) (x @ P))[j] + (id (α := Tensor α [k]) (y @ Q))[j]
  ·
    apply (GetDot.eq.Sum_MulGetS.une _ _ j).trans
    rw [Fin.sum_univ_add]
    have h1 : (∑ i : Fin n, (x ++ y)[Fin.castAdd m i] * id (α := Tensor α []) (P ++ Q)[Fin.castAdd m i][j]) = ∑ i : Fin n, x[i] * id (α := Tensor α []) P[i][j] := by
      apply Fin.Sum.of.All_Eq
      intro i
      apply congrArg₂ (fun (a b : Tensor α []) => id (α := Tensor α []) a * b)
      ·
        simpa [GetElem.getElem, Fin.castAdd] using GetAppend.eq.Get.of.Lt (A := x) (B := y) i.isLt
      ·
        apply congrArg (fun t : Tensor α [k] => (t[j] : Tensor α []))
        simpa [GetElem.getElem, Fin.castAdd] using GetAppend.eq.Get.of.Lt (A := P) (B := Q) i.isLt
    have h2 : (∑ i : Fin m, (x ++ y)[Fin.natAdd n i] * id (α := Tensor α []) (P ++ Q)[Fin.natAdd n i][j]) = ∑ i : Fin m, y[i] * id (α := Tensor α []) Q[i][j] := by
      apply Fin.Sum.of.All_Eq
      intro i
      apply congrArg₂ (fun (a b : Tensor α []) => id (α := Tensor α []) a * b)
      ·
        simpa [GetElem.getElem, Fin.natAdd, Nat.add_sub_cancel_left] using GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := x) (B := y) (Nat.le_add_right n (i : ℕ)) (Nat.add_lt_add_left i.isLt n)
      ·
        apply congrArg (fun t : Tensor α [k] => (t[j] : Tensor α []))
        simpa [GetElem.getElem, Fin.natAdd, Nat.add_sub_cancel_left] using GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := P) (B := Q) (Nat.le_add_right n (i : ℕ)) (Nat.add_lt_add_left i.isLt n)
    erw [h1, h2, ← GetDot.eq.Sum_MulGetS.une x P j, ← GetDot.eq.Sum_MulGetS.une y Q j]
    rfl
  ·
    symm
    apply @Tensor.GetAdd.eq.AddGetS.fin


-- created on 2026-08-23
-- updated on 2026-09-10
