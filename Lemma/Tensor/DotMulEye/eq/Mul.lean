import torch.Tensor.prod
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.Mul
open Bool Nat Tensor Vector
set_option maxHeartbeats 500000


private lemma main_mul
  [Semiring α] [CharZero α]
  (a b : Tensor α [n])
  (i p : Fin n) :
  (id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p])) * (id (α := Tensor α []) b[p]) =
    Mul.mul
      (Mul.mul (id (α := Tensor α []) (↑(KroneckerDelta i p) : Tensor α [])) (id (α := Tensor α []) a[p]))
      (id (α := Tensor α []) b[p]) := by
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
    erw [Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]
  simp only [id] at hc ⊢
  rw [hc]
  apply Tensor.Mul (id (α := Tensor α []) _) (id (α := Tensor α []) _)


private lemma main_zero
  [Semiring α] [CharZero α]
  (a b : Tensor α [n])
  (i p : Fin n)
  (hp : p ≠ i) :
  (id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p])) * (id (α := Tensor α []) b[p]) = 0 := by
  rw [main_mul a b i p]
  simp [Delta.eq.Ite, Ne.symm hp]
  erw [Nat.cast_zero]
  apply Eq.of.EqDataS
  have hmul0 : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
  rw [hmul0, hmul0]
  rw [(rfl : (0 : Tensor α []).data = (0 : List.Vector α [].prod))]
  change (0 : List.Vector α [].prod) * (id (α := Tensor α []) a[p]).data * (id (α := Tensor α []) b[p]).data = 0
  rw [MulZeroClass.zero_mul, MulZeroClass.zero_mul]


private lemma main_one
  [Semiring α] [CharZero α]
  (a b : Tensor α [n])
  (i : Fin n) :
  (id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][i])) * (id (α := Tensor α []) b[i]) =
    (id (α := Tensor α []) a[i]) * (id (α := Tensor α []) b[i]) := by
  rw [main_mul a b i i]
  simp [Delta.eq.Ite]
  erw [Nat.cast_one]
  apply Eq.trans _ (Tensor.Mul (id (α := Tensor α []) a[i]) (id (α := Tensor α []) b[i])).symm
  apply Eq.of.EqDataS
  have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
  rw [hmul, hmul]
  rw [(rfl : (1 : Tensor α []).data = (1 : List.Vector α [].prod))]
  change (1 : List.Vector α [].prod) * (id (α := Tensor α []) a[i]).data * (id (α := Tensor α []) b[i]).data =
    (Mul.mul (id (α := Tensor α []) a[i]) (id (α := Tensor α []) b[i])).data
  rw [one_mul]
  rfl


private lemma main_sum
  [Semiring α] [CharZero α]
  (a b : Tensor α [n])
  (i : Fin n) :
  ∑ p : Fin n, (id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p])) * (id (α := Tensor α []) b[p]) =
    (id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][i])) * (id (α := Tensor α []) b[i]) := by
  apply Finset.sum_eq_single i
  ·
    intro p _ hp
    apply main_zero a b i p hp
  ·
    intro hi
    apply (hi (Finset.mem_univ i)).elim


/--
`(I * a) @ b = a * b` for a broadcast row `a`.
-/
@[path]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (a b : Tensor α [n]) :
-- imply
  ((Tensor.eye n : Tensor α [n, n]) * [_ < n] a) @ b = a * b := by
-- proof
  let M : Tensor α [n, n] := (Tensor.eye n : Tensor α [n, n]) * ([_ < n] a)
  have hstack : (cast (by simp [matmul_shape]) (M @ b) : Tensor α [n]) = [j < n] ∑ p : Fin n, (id (α := Tensor α []) M[j][p]) * (id (α := Tensor α []) b[p]) := by
    apply Eq.of.EqDataS
    apply Eq.of.SEq
    apply (DataCast.as.Data.of.Eq (by simp [matmul_shape]) (M @ b)).trans
    apply SEq.of.Eq
    apply congrArg Tensor.data
    apply Dot.eq.Stack_Sum_MulGetS.mv
  apply Tensor.Eq.of.All_EqGetS.fin
  intro i
  have hL : (cast (by simp [matmul_shape]) (M @ b) : Tensor α [n])[i] = ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) :=
    (congrArg (fun X : Tensor α [n] => X[i]) hstack).trans
      (EqGetStack.fin (fun j : Fin n => ∑ p : Fin n, (id (α := Tensor α []) M[j][p]) * (id (α := Tensor α []) b[p])) i)
  have hR : (a * b)[i] = (id (α := Tensor α []) a[i]) * (id (α := Tensor α []) b[i]) := by
    apply Eq.trans
    ·
      apply Tensor.GetMul.eq.MulGetS.fin
    ·
      apply Eq.symm
      apply Tensor.Mul
  apply Eq.trans hL
  apply Eq.trans _ hR.symm
  simp only [M]
  rw [main_sum a b i]
  apply main_one a b i


-- created on 2023-09-18
-- updated on 2026-09-05
