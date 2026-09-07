import Lemma.Tensor.Det.of.Eq
import Lemma.Tensor.DetAppendHstackS.eq.MulDetS
import Lemma.Tensor.DetDot.eq.MulPowNeg1Mul
import Lemma.Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS
import Lemma.Tensor.EqDot0_0
import Lemma.Tensor.EqDot_0'0
import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.EqMul1
import Lemma.Tensor.MulMul.eq.Mul_Mul
open Matrix Tensor


private lemma det_cast_add_comm
  [CommRing α]
  {m n : ℕ}
  (X : Tensor α [m + n, n + m]) :
  id (α := Tensor α []) X.det = id (α := Tensor α []) (cast (congrArg (fun t => Tensor α [t, n + m]) (Nat.add_comm m n)) X : Tensor α [n + m, n + m]).det := by
  unfold Tensor.det
  rw [dif_neg (by simp : ¬[m + n, n + m].length > 2), dif_neg (by simp : ¬[m + n, n + m].length < 2)]
  rw [dif_neg (by simp : ¬[n + m, n + m].length > 2), dif_neg (by simp : ¬[n + m, n + m].length < 2)]
  simp [Nat.add_comm m n]


@[main]
private lemma main
  [CommRing α] [CharZero α]
  {m n : ℕ}
-- given
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n]) :
-- imply
  (C.hstack A ++ B.hstack (0 : Tensor α [n, m])).det =
    (-1) ^ (m * n) * id (α := Tensor α []) A.det * id (α := Tensor α []) B.det := by
-- proof
  let X := C.hstack A ++ B.hstack (0 : Tensor α [n, m])
  let P := (0 : Tensor α [n, m]).hstack (Tensor.eye n) ++ (Tensor.eye m).hstack (0 : Tensor α [m, n])
  let T := A.hstack C ++ (0 : Tensor α [n, m]).hstack B
  have hC0 : id (α := Tensor α [m, m]) (C @ (0 : Tensor α [n, m])) = 0 := by
    simp [id, EqDot_0'0]
  have hAI : id (α := Tensor α [m, m]) (A @ Tensor.eye (α := α) m) = A := by
    simp [id, EqDot_Eye (α := α)]
  have hCI : id (α := Tensor α [m, n]) (C @ Tensor.eye (α := α) n) = C := by
    simp [id, EqDot_Eye (α := α)]
  have hA0 : id (α := Tensor α [m, n]) (A @ (0 : Tensor α [m, n])) = 0 := by
    simp [id, EqDot_0'0]
  have hB0 : id (α := Tensor α [n, m]) (B @ (0 : Tensor α [n, m])) = 0 := by
    simp [id, EqDot_0'0]
  have h0I : id (α := Tensor α [n, m]) ((0 : Tensor α [n, m]) @ Tensor.eye (α := α) m) = 0 := by
    simp [id, EqDot0_0]
  have hBI : id (α := Tensor α [n, n]) (B @ Tensor.eye (α := α) n) = B := by
    simp [id, EqDot_Eye (α := α)]
  have h00 : id (α := Tensor α [n, n]) ((0 : Tensor α [n, m]) @ (0 : Tensor α [m, n])) = 0 := by
    simp [id, EqDot0_0]
  have hprod : X @ P = T := by
    simp [X, P, T]
    rw [DotAppendSHstackS.eq.AppendHstackSAddSDotS, hC0, hAI, hCI, hA0, hB0, h0I, hBI, h00]
    simp [zero_add, add_zero]
    rfl
  have hT := DetAppendHstackS.eq.MulDetS.triu A B C
  have hs : [m + n, n + m] = [n + m, n + m] := by simp [Nat.add_comm]
  let Xsq : Tensor α [n + m, n + m] :=
    cast (congrArg (fun t => Tensor α [t, n + m]) (Nat.add_comm m n)) X
  have hX : Xsq ≃ X := by convert Bool.SEqCast.of.Eq (Vector := Tensor α) hs X
  have hXP : Xsq @ P ≃ X @ P := SEqDotS.of.SEq hX P
  have hXPT : Xsq @ P ≃ T := hXP.trans (Bool.SEq.of.Eq hprod)
  have hdot := DetDot.eq.MulPowNeg1Mul (m := n) (n := m) Xsq
  have hXdet := (det_cast_add_comm (m := m) (n := n) X).symm
  have hXPdet : id (α := Tensor α []) (Xsq @ P).det = id (α := Tensor α []) T.det := by
    apply Eq.trans (det_cast_add_comm (m := n) (n := m) (Xsq @ P))
    apply congrArg (id (α := Tensor α []))
    apply Det.of.Eq
    apply Eq.trans _ (SEq.cast hXPT)
    apply eq_of_heq
    apply HEq.trans (cast_heq _ _)
    exact (cast_heq _ _).symm
  have hneg : ((-1 : Tensor α []) ^ (2 * (m * n))) = 1 :=
    Even.neg_one_pow (even_two_mul (m * n))
  have hdot' : id (α := Tensor α []) (Xsq @ P).det =
      ((-1 : Tensor α []) ^ (m * n)) * id (α := Tensor α []) X.det := by
    simp only [id] at hdot hXdet ⊢
    rw [hdot, Nat.mul_comm n m, hXdet]
    rfl
  have hsign : id (α := Tensor α []) X.det =
      ((-1 : Tensor α []) ^ (m * n)) * id (α := Tensor α []) T.det := by
    calc
      id (α := Tensor α []) X.det
          = (1 : Tensor α []) * id (α := Tensor α []) X.det :=
            (Tensor.EqMul1 (id (α := Tensor α []) X.det)).symm
      _ = ((-1 : Tensor α []) ^ (2 * (m * n))) * id (α := Tensor α []) X.det := by
            rw [hneg]
      _ = ((-1 : Tensor α []) ^ (m * n + m * n)) * id (α := Tensor α []) X.det := by
            rw [two_mul]
      _ = (((-1 : Tensor α []) ^ (m * n)) * ((-1 : Tensor α []) ^ (m * n))) *
            id (α := Tensor α []) X.det := by
            rw [pow_add,
              show
                HMul.hMul (γ := Tensor α []) (self := instHMul)
                  ((-1 : Tensor α []) ^ (m * n))
                  ((-1 : Tensor α []) ^ (m * n)) =
                HMul.hMul (γ := Tensor α [])
                  (self := instHMulTensorNilNatOfMul)
                  ((-1 : Tensor α []) ^ (m * n))
                  ((-1 : Tensor α []) ^ (m * n)) from
                (Tensor.Mul ((-1 : Tensor α []) ^ (m * n))
                  ((-1 : Tensor α []) ^ (m * n))).symm]
      _ = ((-1 : Tensor α []) ^ (m * n)) *
            (((-1 : Tensor α []) ^ (m * n)) * id (α := Tensor α []) X.det) :=
            Tensor.MulMul.eq.Mul_Mul _ _ _
      _ = ((-1 : Tensor α []) ^ (m * n)) * id (α := Tensor α []) (Xsq @ P).det := by
            rw [← hdot']
      _ = ((-1 : Tensor α []) ^ (m * n)) * id (α := Tensor α []) T.det := by
            rw [hXPdet]
  show id (α := Tensor α []) X.det =
      (-1) ^ (m * n) * id (α := Tensor α []) A.det * id (α := Tensor α []) B.det
  rw [hsign, hT]
  exact (Tensor.MulMul.eq.Mul_Mul _ _ _).symm


-- created on 2020-08-19
-- updated on 2026-09-07
