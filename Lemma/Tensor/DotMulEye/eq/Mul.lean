import Lemma.Bool.SEq.is.Eq
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.DataCast.as.Data.of.Eq
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetEye.eq.Delta
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Vector.Map₂.eq.Map.of.Eq_1
open Bool Nat Tensor
set_option maxHeartbeats 400000


private lemma hmul_eq_mul
  [Mul α]
  (x y : Tensor α []) :
  id (α := Tensor α []) x * id (α := Tensor α []) y = Mul.mul (id (α := Tensor α []) x) (id (α := Tensor α []) y) := by
  apply Eq.of.EqDataS
  simp [id, HMul.hMul, Mul.mul]
  erw [Vector.Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]
  rfl


private lemma mul_cast_one
  [Semiring α]
  (x y : Tensor α []) :
  Mul.mul (Mul.mul (↑(1 : ℕ) : Tensor α []) x) y = Mul.mul x y := by
  have h1 : (↑(1 : ℕ) : Tensor α []) = (1 : Tensor α []) := Nat.cast_one
  rw [h1]
  apply Eq.of.EqDataS
  have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
  rw [hmul, hmul]
  have ho : (1 : Tensor α []).data = (1 : List.Vector α [].prod) := rfl
  rw [ho]
  change (1 : List.Vector α [].prod) * x.data * y.data = (Mul.mul x y).data
  rw [one_mul]
  rfl


private lemma eye_mul_broadcast_get
  [Semiring α] [CharZero α]
  (a : Tensor α [n])
  (i p : Fin n) :
  id (α := Tensor α []) (((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p]) =
    Mul.mul
      (id (α := Tensor α []) (↑(KroneckerDelta i p) : Tensor α []))
      (id (α := Tensor α []) a[p]) := by
  have hrow := GetMul.eq.MulGetS (Tensor.eye n : Tensor α [n, n]) ([_ < n] a) i
  have hA := EqGetStack (fun _ : Fin n => a) i
  have hd := GetEye.eq.Delta (α := α) i p
  have hcell := GetMul.eq.MulGetS ((Tensor.eye n : Tensor α [n, n])[i]) (([_ < n] a)[i]) p
  have h1 :
      ((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a))[i][p] =
        ((Tensor.eye n : Tensor α [n, n])[i] * ([_ < n] a)[i])[p] :=
    congrArg (fun X : Tensor α [n] => X[p]) hrow
  erw [h1, hcell, hA, hd]
  apply Eq.of.EqDataS
  simp [id, HMul.hMul, Mul.mul]
  erw [Vector.Map₂.eq.Map.of.Eq_1 (n := [].prod) (by rfl)]


/--
`(I * a) @ b = a * b` for a broadcast row `a`.
-/
@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (a b : Tensor α [n]) :
-- imply
  ((Tensor.eye n : Tensor α [n, n]) * ([_ < n] a)) @ b = a * b := by
-- proof
  let M : Tensor α [n, n] := (Tensor.eye n : Tensor α [n, n]) * ([_ < n] a)
  have h := Dot.eq.Stack_Sum_MulGetS.mv M b
  have hshape : matmul_shape [n, n] [n] = [n] := by simp [matmul_shape]
  have hstack : (cast (by simp [matmul_shape]) (M @ b) : Tensor α [n]) = [i < n] ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) := by
    apply Eq.of.EqDataS
    apply Eq.of.SEq
    have hcast := DataCast.as.Data.of.Eq hshape (M @ b)
    have hd := SEq.of.Eq (congrArg Tensor.data h)
    exact hcast.trans hd
  apply Eq.of.All_EqGetS.fin
  intro i
  have hsum := EqGetStack.fin
    (fun i : Fin n => ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p])) i
  have hL : (cast (by simp [matmul_shape]) (M @ b) : Tensor α [n])[i] = ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) :=
    (congrArg (fun X : Tensor α [n] => X[i]) hstack).trans hsum
  have hR : (a * b)[i] = (id (α := Tensor α []) a[i]) * (id (α := Tensor α []) b[i]) := by
    have hb := GetMul.eq.MulGetS.fin a b i
    exact hb.trans (hmul_eq_mul a[i] b[i]).symm
  refine Eq.trans hL ?_
  refine Eq.trans ?_ hR.symm
  have hMp (p : Fin n) :
      (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) =
        Mul.mul
          (Mul.mul (id (α := Tensor α []) (↑(KroneckerDelta i p) : Tensor α [])) (id (α := Tensor α []) a[p]))
          (id (α := Tensor α []) b[p]) := by
    simp only [M]
    have hc := eye_mul_broadcast_get a i p
    simp only [id] at hc ⊢
    rw [hc]
    exact hmul_eq_mul _ _
  have hsingle : ∑ p : Fin n, (id (α := Tensor α []) M[i][p]) * (id (α := Tensor α []) b[p]) = (id (α := Tensor α []) M[i][i]) * (id (α := Tensor α []) b[i]) := by
    apply Finset.sum_eq_single i
    ·
      intro p _ hp
      rw [hMp p]
      have hip : i ≠ p := by
        intro h
        exact hp h.symm
      have hδ : KroneckerDelta i p = 0 := by
        simp [Delta.eq.Ite, hip]
      rw [hδ]
      have h0 : (↑(0 : ℕ) : Tensor α []) = (0 : Tensor α []) := Nat.cast_zero
      rw [h0]
      apply Eq.of.EqDataS
      have hmul0 : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
      rw [hmul0, hmul0]
      have hz : (0 : Tensor α []).data = (0 : List.Vector α [].prod) := rfl
      rw [hz]
      change (0 : List.Vector α [].prod) * (id (α := Tensor α []) a[p]).data * (id (α := Tensor α []) b[p]).data = 0
      rw [zero_mul, zero_mul]
    ·
      intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsingle]
  rw [hMp i]
  simp [Delta.eq.Ite]
  exact (mul_cast_one a[i] b[i]).trans (hmul_eq_mul a[i] b[i]).symm


-- created on 2023-09-18
-- updated on 2026-08-27
