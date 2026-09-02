import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.GetMulEye_Stack.eq.MulDelta
import Lemma.Tensor.GetTranspose.eq.Get
import Lemma.Tensor.Mul
import sympy.matrices.expressions.special
open Nat Tensor
set_option maxHeartbeats 4000000


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.TMulEye.eq.MulEye |
| comm | Tensor.MulEye.eq.TMulEye |
-/
@[main, comm]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [d]) :
-- imply
  ((Tensor.eye d : Tensor α [d, d]) * [_ < d] x)ᵀ = (Tensor.eye d : Tensor α [d, d]) * [_ < d] x := by
-- proof
  let I : Tensor α [d, d] := Tensor.eye d
  let M : Tensor α [d, d] := I * [_ < d] x
  change Mᵀ = M
  apply Eq.of.All_EqGetS.fin
  intro i
  apply Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [GetTranspose.eq.Get.fin]
  have hL := (GetMulEye_Stack.eq.MulDelta x j i).trans (Tensor.Mul (↑(KroneckerDelta j i) : Tensor α []) (id (α := Tensor α []) x[i]))
  have hR := (GetMulEye_Stack.eq.MulDelta x i j).trans (Tensor.Mul (↑(KroneckerDelta i j) : Tensor α []) (id (α := Tensor α []) x[j]))
  simp only [id, M, I] at hL hR ⊢
  refine hL.trans (Eq.trans ?_ hR.symm)
  have hδ : (↑(KroneckerDelta j i) : Tensor α []) = (↑(KroneckerDelta i j) : Tensor α []) := by
    simp [KroneckerDelta, Fin.ext_iff, eq_comm]
  rw [hδ]
  if hij : i = j then
    simp [hij]
  else
    simp [hij, Delta.eq.Ite]
    have h0 : (↑(0 : ℕ) : Tensor α []) = (0 : Tensor α []) := Nat.cast_zero
    rw [h0]
    apply Eq.of.EqDataS
    have hmul : ∀ A B : Tensor α [], (Mul.mul A B).data = A.data * B.data := fun _ _ => rfl
    rw [hmul, hmul]
    have hz : (0 : Tensor α []).data = (0 : List.Vector α [].prod) := rfl
    rw [hz]
    rw [zero_mul, zero_mul]


-- created on 2026-09-02
