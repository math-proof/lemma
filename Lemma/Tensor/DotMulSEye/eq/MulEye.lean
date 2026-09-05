import Lemma.Finset.MulSum.eq.Sum_Mul
import Lemma.Fin.Sum_MulDeltaS.eq.Delta
import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetDot.eq.Sum_MulGetS
import Lemma.Tensor.GetMul.eq.MulGetS
import Lemma.Tensor.GetMulEye_Stack.eq.MulDelta
import Lemma.Tensor.Mul
import sympy.matrices.expressions.special
open Finset Nat Tensor Fin
set_option maxHeartbeats 800000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.DotMulSEye.eq.MulEye |
| comm | Tensor.MulEye.eq.DotMulSEye |
-/
@[main, comm]
private lemma main
  [CommSemiring α] [CharZero α]
-- given
  (a b : Tensor α [d]) :
-- imply
  (Tensor.eye d * [_ < d] a) @ (Tensor.eye d * [_ < d] b) = Tensor.eye d * [_ < d] (a * b) := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  have hL := Eq.trans rfl (GetDot.eq.Sum_MulGetS (Tensor.eye (α := α) d * [_ < d] a) (Tensor.eye (α := α) d * [_ < d] b) i j)
  simp only [id] at hL ⊢
  refine hL.trans ?_
  have hterm (k : Fin d) : id (α := Tensor α []) ((Tensor.eye (α := α) d * [_ < d] a)[i][k]) * id (α := Tensor α []) ((Tensor.eye (α := α) d * [_ < d] b)[k][j]) = Mul.mul (Mul.mul (↑(KroneckerDelta i k) : Tensor α []) (id (α := Tensor α []) a[k])) (Mul.mul (↑(KroneckerDelta k j) : Tensor α []) (id (α := Tensor α []) b[j])) := by
    have ha := (GetMulEye_Stack.eq.MulDelta a i k).trans (Tensor.Mul (↑(KroneckerDelta i k) : Tensor α []) (id (α := Tensor α []) a[k]))
    have hb := (GetMulEye_Stack.eq.MulDelta b k j).trans (Tensor.Mul (↑(KroneckerDelta k j) : Tensor α []) (id (α := Tensor α []) b[j]))
    simp only [id] at ha hb ⊢
    rw [ha, hb]
    exact Tensor.Mul (id (α := Tensor α []) _) (id (α := Tensor α []) _)
  have hsum : (∑ k : Fin d, id (α := Tensor α []) ((Tensor.eye (α := α) d * [_ < d] a)[i][k]) * id (α := Tensor α []) ((Tensor.eye (α := α) d * [_ < d] b)[k][j])) = ∑ k : Fin d, Mul.mul (Mul.mul (↑(KroneckerDelta k i) : Tensor α []) (id (α := Tensor α []) a[i])) (Mul.mul (↑(KroneckerDelta k j) : Tensor α []) (id (α := Tensor α []) b[j])) := by
    apply Finset.sum_congr rfl
    intro k _
    refine (hterm k).trans ?_
    refine congrArg₂ Mul.mul ?_ rfl
    refine Eq.trans ?_ (congrArg (fun δ => Mul.mul δ (id (α := Tensor α []) a[i])) (by simp [KroneckerDelta, Fin.ext_iff, eq_comm] : (↑(KroneckerDelta i k) : Tensor α []) = ↑(KroneckerDelta k i)))
    if h : i = k then
      simp [h]
    else
      simp [h, Delta.eq.Ite]
      erw [Nat.cast_zero]
      apply Eq.of.EqDataS
      have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
      rw [hmul, hmul]
      have hz : (0 : Tensor α []).data = (0 : List.Vector α [].prod) := rfl
      rw [hz, zero_mul, zero_mul]
  refine hsum.trans ?_
  erw [sum_congr rfl fun u _ => mul_mul_mul_comm (↑(KroneckerDelta u i) : Tensor α []) (id (α := Tensor α []) a[i]) (↑(KroneckerDelta u j) : Tensor α []) (id (α := Tensor α []) b[j])]
  erw [Sum_Mul.eq.MulSum]
  erw [Sum_MulDeltaS.eq.Delta]
  have hR := (GetMulEye_Stack.eq.MulDelta (a * b) i j).trans (Tensor.Mul (↑(KroneckerDelta i j) : Tensor α []) (id (α := Tensor α []) (a * b)[j]))
  simp only [id] at hR
  refine Eq.trans ?_ hR.symm
  have hidx : Mul.mul (↑(KroneckerDelta i j) : Tensor α []) (Mul.mul (id (α := Tensor α []) a[i]) (id (α := Tensor α []) b[j])) = Mul.mul (↑(KroneckerDelta i j) : Tensor α []) (Mul.mul (id (α := Tensor α []) a[j]) (id (α := Tensor α []) b[j])) := by
    if h : i = j then
      simp [h]
    else
      simp [h, Delta.eq.Ite]
      erw [Nat.cast_zero]
      apply Eq.of.EqDataS
      have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
      have hz : (0 : Tensor α []).data = (0 : List.Vector α [].prod) := rfl
      rw [hmul, hmul, hz]
      change (0 : List.Vector α [].prod) * _ = (0 : List.Vector α [].prod) * _
      rw [zero_mul, zero_mul]
  refine hidx.trans ?_
  refine congrArg (fun x => Mul.mul (↑(KroneckerDelta i j) : Tensor α []) x) ?_
  have hmul : id (α := Tensor α []) (Mul.mul a b)[j] = Mul.mul (id (α := Tensor α []) a[j]) (id (α := Tensor α []) b[j]) := by
    have h := GetMul.eq.MulGetS.fin (A := a) (B := b) (i := j)
    simp only [id]
    exact h
  exact hmul.symm.trans (by simp only [id]; rfl)


-- created on 2026-09-02
