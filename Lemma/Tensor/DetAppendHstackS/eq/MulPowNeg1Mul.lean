import Lemma.Tensor.Det.of.Eq
import Lemma.Tensor.DetDot.eq.MulPowNeg1Mul
import Lemma.Tensor.DotAppendSHstackS.eq.AppendHstackSAddSDotS
import Lemma.Tensor.Eq.is.ToMatrix
import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.EqMul1
import Lemma.Tensor.MulMul.eq.Mul_Mul
open Matrix Tensor
set_option maxHeartbeats 800000


private lemma toMatrix_zero
  [NonUnitalNonAssocSemiring α] {m n : ℕ} :
  (0 : Tensor α [m, n]).toMatrix = 0 := by
  ext i j
  have hz := EqGet0_0.fin (α := α) (s := [m, n]) ⟨(i : ℕ), i.isLt⟩
  have hz' := EqGet0_0.fin (α := α) (s := [n]) ⟨(j : ℕ), j.isLt⟩
  simp [Tensor.toMatrix, GetElem.getElem] at hz hz' ⊢
  rw [hz]
  exact hz'


private lemma dot_zero
  [NonUnitalNonAssocSemiring α]
  {m l n : ℕ}
  (A : Tensor α [m, l]) :
  (A @ (0 : Tensor α [l, n]) : Tensor α [m, n]) = 0 :=
  Eq.of.ToMatrix (by
    apply Eq.trans (ToMatrixDot.eq.MulToMatrixS A (0 : Tensor α [l, n]))
    apply Eq.trans (congrArg (HMul.hMul A.toMatrix) toMatrix_zero)
    apply Eq.trans (Matrix.mul_zero A.toMatrix)
    exact toMatrix_zero.symm)


private lemma zero_dot
  [NonUnitalNonAssocSemiring α]
  {m l n : ℕ}
  (A : Tensor α [l, n]) :
  ((0 : Tensor α [m, l]) @ A : Tensor α [m, n]) = 0 :=
  Eq.of.ToMatrix (by
    apply Eq.trans (ToMatrixDot.eq.MulToMatrixS (0 : Tensor α [m, l]) A)
    apply Eq.trans (congrArg (fun M => HMul.hMul M A.toMatrix) toMatrix_zero)
    apply Eq.trans (Matrix.zero_mul A.toMatrix)
    exact toMatrix_zero.symm)


private lemma det_cast_add_comm
  [CommRing α]
  {m n : ℕ}
  (X : Tensor α [m + n, n + m]) :
  id (α := Tensor α []) X.det =
    id (α := Tensor α [])
      (cast (congrArg (fun t => Tensor α [t, n + m]) (Nat.add_comm m n)) X : Tensor α [n + m, n + m]).det := by
  unfold Tensor.det
  rw [dif_neg (by simp : ¬[m + n, n + m].length > 2), dif_neg (by simp : ¬[m + n, n + m].length < 2)]
  rw [dif_neg (by simp : ¬[n + m, n + m].length > 2), dif_neg (by simp : ¬[n + m, n + m].length < 2)]
  simp [Nat.add_comm m n]


private lemma get_blockUpper_castAdd_castAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n])
  (i j : Fin m) :
  id (α := Tensor α [])
      (A.hstack C ++ (0 : Tensor α [n, m]).hstack B)[Fin.castAdd n i][Fin.castAdd n j] =
    id (α := Tensor α []) A[i][j] := by
  have hrow :=
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack C) ((0 : Tensor α [n, m]).hstack B)
  have hcell := GetHstack.eq.Get.of.Lt j.isLt A C i
  simp only [id] at hcell ⊢
  apply Eq.trans
    (congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α [])
          (t[(j : ℕ)]'(by
            simp only [Tensor.length]
            exact Nat.lt_add_right n j.isLt)))
      hrow)
  simp only [id]
  simpa [GetElem.getElem] using hcell


private lemma get_blockUpper_castAdd_natAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n])
  (i : Fin m)
  (j : Fin n) :
  id (α := Tensor α [])
      (A.hstack C ++ (0 : Tensor α [n, m]).hstack B)[Fin.castAdd n i][Fin.natAdd m j] =
    id (α := Tensor α []) C[i][j] := by
  have hrow :=
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack C) ((0 : Tensor α [n, m]).hstack B)
  have hcell := GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val) (Fin.natAdd m j).isLt A C i
  simp only [id] at hcell ⊢
  apply Eq.trans
    (congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α [])
          (t[(Fin.natAdd m j : ℕ)]'(by
            simp only [Tensor.length]
            exact (Fin.natAdd m j).isLt)))
      hrow)
  simp only [id]
  simpa [GetElem.getElem, Fin.val_natAdd, Nat.add_sub_cancel_left] using hcell


private lemma get_blockUpper_natAdd_castAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n])
  (i : Fin n)
  (j : Fin m) :
  id (α := Tensor α [])
      (A.hstack C ++ (0 : Tensor α [n, m]).hstack B)[Fin.natAdd m i][Fin.castAdd n j] =
    0 := by
  have hrow :=
    GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [m + n]) (Nat.le_add_right m i.val)
      (Fin.natAdd m i).isLt (A.hstack C) ((0 : Tensor α [n, m]).hstack B)
  have hcell := GetHstack.eq.Get.of.Lt j.isLt (0 : Tensor α [n, m]) B i
  have hz := EqGet0_0.fin (α := α) (s := [n, m]) ⟨(i : ℕ), i.isLt⟩
  have hz' := EqGet0_0.fin (α := α) (s := [m]) ⟨(j : ℕ), j.isLt⟩
  simp only [id] at hcell ⊢
  apply Eq.trans
    (congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α [])
          (t[(j : ℕ)]'(by
            simp only [Tensor.length]
            exact Nat.lt_add_right n j.isLt)))
      hrow)
  simp only [id, Nat.add_sub_cancel_left]
  apply Eq.trans hcell
  simp [GetElem.getElem] at hz hz' ⊢
  rw [hz]
  exact hz'


private lemma get_blockUpper_natAdd_natAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n])
  (i j : Fin n) :
  id (α := Tensor α [])
      (A.hstack C ++ (0 : Tensor α [n, m]).hstack B)[Fin.natAdd m i][Fin.natAdd m j] =
    id (α := Tensor α []) B[i][j] := by
  have hrow :=
    GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [m + n]) (Nat.le_add_right m i.val)
      (Fin.natAdd m i).isLt (A.hstack C) ((0 : Tensor α [n, m]).hstack B)
  have hcell :=
    GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val) (Fin.natAdd m j).isLt
      (0 : Tensor α [n, m]) B i
  simp only [id] at hcell ⊢
  apply Eq.trans
    (congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α [])
          (t[(Fin.natAdd m j : ℕ)]'(by
            simp only [Tensor.length]
            exact (Fin.natAdd m j).isLt)))
      hrow)
  simp only [id, Nat.add_sub_cancel_left]
  simpa [GetElem.getElem, Fin.val_natAdd] using hcell


private lemma det_blockUpper
  [CommRing α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n]) :
  id (α := Tensor α []) (A.hstack C ++ (0 : Tensor α [n, m]).hstack B).det =
    id (α := Tensor α []) A.det * id (α := Tensor α []) B.det := by
  let T := A.hstack C ++ (0 : Tensor α [n, m]).hstack B
  apply Eq.trans (congrArg (id (α := Tensor α [])) (Det.eq.DetToMatrix T))
  have hT :
      T.toMatrix =
        (reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A.toMatrix C.toMatrix 0 B.toMatrix)) := by
    ext i j
    simp [T, Tensor.toMatrix, Matrix.reindex, Matrix.submatrix]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockUpper_castAdd_castAdd A B C i j
      · simp [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
          fromBlocks_apply₁₂, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockUpper_castAdd_natAdd A B C i j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
          fromBlocks_apply₂₁]
        simpa [GetElem.getElem, id] using get_blockUpper_natAdd_castAdd A B C i j
      · simp [finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockUpper_natAdd_natAdd A B C i j
  rw [hT, det_reindex_self, det_fromBlocks_zero₂₁]
  rw [← Det.eq.DetToMatrix A, ← Det.eq.DetToMatrix B]
  simp only [id]
  erw [Tensor.Mul]
  rfl


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
    simp [id, dot_zero]; rfl
  have hAI : id (α := Tensor α [m, m]) (A @ Tensor.eye (α := α) m) = A := by
    simp [id, EqDot_Eye (α := α)]
  have hCI : id (α := Tensor α [m, n]) (C @ Tensor.eye (α := α) n) = C := by
    simp [id, EqDot_Eye (α := α)]
  have hA0 : id (α := Tensor α [m, n]) (A @ (0 : Tensor α [m, n])) = 0 := by
    simp [id, dot_zero]; rfl
  have hB0 : id (α := Tensor α [n, m]) (B @ (0 : Tensor α [n, m])) = 0 := by
    simp [id, dot_zero]; rfl
  have h0I : id (α := Tensor α [n, m]) ((0 : Tensor α [n, m]) @ Tensor.eye (α := α) m) = 0 := by
    simp [id, zero_dot]; rfl
  have hBI : id (α := Tensor α [n, n]) (B @ Tensor.eye (α := α) n) = B := by
    simp [id, EqDot_Eye (α := α)]
  have h00 : id (α := Tensor α [n, n]) ((0 : Tensor α [n, m]) @ (0 : Tensor α [m, n])) = 0 := by
    simp [id, zero_dot]; rfl
  have hprod : X @ P = T := by
    simp [X, P, T]
    rw [DotAppendSHstackS.eq.AppendHstackSAddSDotS, hC0, hAI, hCI, hA0, hB0, h0I, hBI, h00]
    simp [zero_add, add_zero]
    rfl
  have hT := det_blockUpper A B C
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
-- updated on 2026-09-06
