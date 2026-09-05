import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.Mul
import Lemma.Vector.Map₂.eq.Map.of.Eq_1
open Bool Nat Tensor
set_option maxHeartbeats 1000000


/--
`(I * a) @ b = a * b` for a broadcast row `a`.
-/
@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (a b : Tensor α [n]) :
-- imply
  ((Tensor.eye n : Tensor α [n, n]) * [_ < n] a) @ b = a * b := by
-- proof
  let M : Tensor α [n, n] := (Tensor.eye n : Tensor α [n, n]) * ([_ < n] a)
  have hstack : (cast (by simp [matmul_shape]) ((M) @ (b)) : Tensor α [n]) = [j < n] ∑ p : Fin n, (id (α := Tensor α []) M[j][p]) * (id (α := Tensor α []) b[p]) := by
    apply Eq.of.EqDataS
    apply Eq.of.SEq
    apply (DataCast.as.Data.of.Eq (by simp [matmul_shape]) ((M) @ (b))).trans
    apply SEq.of.Eq
    apply congrArg Tensor.data
    apply Dot.eq.Stack_Sum_MulGetS.mv
  apply Eq.of.All_EqGetS.fin
  intro i
  have hL : (cast (by simp [matmul_shape]) ((M) @ (b)) : Tensor α [n])[i] = ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) :=
    (congrArg (fun X : Tensor α [n] => X[i]) hstack).trans
      (EqGetStack.fin (fun j : Fin n => ∑ p : Fin n, (id (α := Tensor α []) M[j][p]) * (id (α := Tensor α []) b[p])) i)
  have hR : (a * b)[i] = (id (α := Tensor α []) a[i]) * (id (α := Tensor α []) b[i]) := by
    apply Eq.trans
    ·
      apply GetMul.eq.MulGetS.fin
    ·
      apply Eq.symm
      apply Tensor.Mul
  apply Eq.trans hL
  apply Eq.trans _ hR.symm
  have hMp (p : Fin n) :
      (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) =
        Mul.mul
          (Mul.mul (id (α := Tensor α []) (↑(KroneckerDelta i p) : Tensor α [])) (id (α := Tensor α []) a[p]))
          (id (α := Tensor α []) b[p]) := by
    simp only [M]
    have hrow := GetMul.eq.MulGetS (Tensor.eye n : Tensor α [n, n]) ([_ < n] a) i
    have hA := EqGetStack (fun _ : Fin n => a) i
    have hd := GetEye.eq.Delta (α := α) i p
    have hcell := GetMul.eq.MulGetS ((Tensor.eye n : Tensor α [n, n])[i]) (([_ < n] a)[i]) p
    have h1 :
        ((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p] =
          ((Tensor.eye n : Tensor α [n, n])[i] * ([_ < n] a)[i])[p] :=
      congrArg (fun X : Tensor α [n] => X[p]) hrow
    have hc :
        id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p]) =
          Mul.mul
            (id (α := Tensor α []) (↑(KroneckerDelta i p) : Tensor α []))
            (id (α := Tensor α []) a[p]) := by
      erw [h1, hcell, hA, hd]
      apply Eq.of.EqDataS
      simp [id, HMul.hMul, Mul.mul]
      erw [Vector.Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]
    simp only [id] at hc ⊢
    rw [hc]
    apply Tensor.Mul (id (α := Tensor α []) _) (id (α := Tensor α []) _)
  have hsingle : ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) = (id (α := Tensor α []) M[i][i]) * (id (α := Tensor α []) b[i]) := by
    apply Finset.sum_eq_single i
    ·
      intro p _ hp
      rw [hMp p]
      simp [Delta.eq.Ite, Ne.symm hp]
      erw [Nat.cast_zero]
      apply Eq.of.EqDataS
      have hmul0 : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
      rw [hmul0, hmul0]
      rw [(rfl : (0 : Tensor α []).data = (0 : List.Vector α [].prod))]
      change (0 : List.Vector α [].prod) * (id (α := Tensor α []) a[p]).data * (id (α := Tensor α []) b[p]).data = 0
      rw [zero_mul, zero_mul]
    ·
      intro hi
      apply (hi (Finset.mem_univ i)).elim
  rw [hsingle]
  rw [hMp i]
  simp [Delta.eq.Ite]
  erw [Nat.cast_one]
  apply Eq.trans _ (Tensor.Mul (id (α := Tensor α []) a[i]) (id (α := Tensor α []) b[i])).symm
  apply Eq.of.EqDataS
  have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
  rw [hmul, hmul]
  rw [(rfl : (1 : Tensor α []).data = (1 : List.Vector α [].prod))]
  change (1 : List.Vector α [].prod) * (id (α := Tensor α []) a[i]).data * (id (α := Tensor α []) b[i]).data = (Mul.mul (id (α := Tensor α []) a[i]) (id (α := Tensor α []) b[i])).data
  rw [one_mul]
  rfl


-- created on 2023-09-18
-- updated on 2026-09-05
