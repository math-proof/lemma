import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Lemma.Tensor.Det.eq.DetToMatrix
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.Mul
import sympy.matrices.dense
import sympy.matrices.determinant
open Matrix Tensor


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
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack C)
      ((0 : Tensor α [n, m]).hstack B)
  have hcell := GetHstack.eq.Get.of.Lt j.isLt A C i
  have hj := Nat.lt_add_right n j.isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(j : ℕ)]'hj))
      hrow
  simp only [id] at hget
  simpa [GetElem.getElem] using hget.trans hcell


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
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack C)
      ((0 : Tensor α [n, m]).hstack B)
  have hcell :=
    GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val)
      (Fin.natAdd m j).isLt A C i
  have hj := (Fin.natAdd m j).isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(Fin.natAdd m j : ℕ)]'hj))
      hrow
  simp only [id] at hget
  simpa [GetElem.getElem, Fin.val_natAdd, Nat.add_sub_cancel_left] using hget.trans hcell


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
  have hj := Nat.lt_add_right n j.isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(j : ℕ)]'hj))
      hrow
  simp only [id, Nat.add_sub_cancel_left] at hget
  apply Eq.trans hget
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
    GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val)
      (Fin.natAdd m j).isLt (0 : Tensor α [n, m]) B i
  have hj := (Fin.natAdd m j).isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(Fin.natAdd m j : ℕ)]'hj))
      hrow
  simp only [id, Nat.add_sub_cancel_left] at hget
  simpa [GetElem.getElem, Fin.val_natAdd] using hget.trans hcell


/--
Determinant of a block-upper-triangular tensor:
`det [A C; 0 B] = det A * det B`.
-/
@[main]
private lemma triu
  [CommRing α]
  {m n : ℕ}
-- given
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [m, n]) :
-- imply
  id (α := Tensor α []) (A.hstack C ++ (0 : Tensor α [n, m]).hstack B).det =
    id (α := Tensor α []) A.det * id (α := Tensor α []) B.det := by
-- proof
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


private lemma get_blockLower_castAdd_castAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [n, m])
  (i j : Fin m) :
  id (α := Tensor α [])
      (A.hstack (0 : Tensor α [m, n]) ++ C.hstack B)[Fin.castAdd n i][Fin.castAdd n j] =
    id (α := Tensor α []) A[i][j] := by
  have hrow :=
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack (0 : Tensor α [m, n]))
      (C.hstack B)
  have hcell := GetHstack.eq.Get.of.Lt j.isLt A (0 : Tensor α [m, n]) i
  have hj := Nat.lt_add_right n j.isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(j : ℕ)]'hj))
      hrow
  simp only [id] at hget
  simpa [GetElem.getElem] using hget.trans hcell


private lemma get_blockLower_castAdd_natAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [n, m])
  (i : Fin m)
  (j : Fin n) :
  id (α := Tensor α [])
      (A.hstack (0 : Tensor α [m, n]) ++ C.hstack B)[Fin.castAdd n i][Fin.natAdd m j] =
    0 := by
  have hrow :=
    GetAppend.eq.Get.of.Lt (s := [m + n]) i.isLt (A.hstack (0 : Tensor α [m, n]))
      (C.hstack B)
  have hcell :=
    GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val)
      (Fin.natAdd m j).isLt A (0 : Tensor α [m, n]) i
  have hz := EqGet0_0.fin (α := α) (s := [m, n]) ⟨(i : ℕ), i.isLt⟩
  have hz' := EqGet0_0.fin (α := α) (s := [n]) ⟨(j : ℕ), j.isLt⟩
  have hj := (Fin.natAdd m j).isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(Fin.natAdd m j : ℕ)]'hj))
      hrow
  simp only [id, Fin.val_natAdd] at hget
  apply Eq.trans hget
  apply Eq.trans hcell
  simp [GetElem.getElem] at hz hz' ⊢
  rw [hz]
  exact hz'


private lemma get_blockLower_natAdd_castAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [n, m])
  (i : Fin n)
  (j : Fin m) :
  id (α := Tensor α [])
      (A.hstack (0 : Tensor α [m, n]) ++ C.hstack B)[Fin.natAdd m i][Fin.castAdd n j] =
    id (α := Tensor α []) C[i][j] := by
  have hrow :=
    GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [m + n]) (Nat.le_add_right m i.val)
      (Fin.natAdd m i).isLt (A.hstack (0 : Tensor α [m, n])) (C.hstack B)
  have hcell := GetHstack.eq.Get.of.Lt j.isLt C B i
  have hj := Nat.lt_add_right n j.isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(j : ℕ)]'hj))
      hrow
  simp only [id, Nat.add_sub_cancel_left] at hget
  simpa [GetElem.getElem] using hget.trans hcell


private lemma get_blockLower_natAdd_natAdd
  [AddCommMonoid α]
  {m n : ℕ}
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [n, m])
  (i j : Fin n) :
  id (α := Tensor α [])
      (A.hstack (0 : Tensor α [m, n]) ++ C.hstack B)[Fin.natAdd m i][Fin.natAdd m j] =
    id (α := Tensor α []) B[i][j] := by
  have hrow :=
    GetAppend.eq.Get_Sub.of.GtAdd.Ge (s := [m + n]) (Nat.le_add_right m i.val)
      (Fin.natAdd m i).isLt (A.hstack (0 : Tensor α [m, n])) (C.hstack B)
  have hcell :=
    GetHstack.eq.Get_Sub.of.GtAdd.Ge (Nat.le_add_right m j.val)
      (Fin.natAdd m j).isLt C B i
  have hj := (Fin.natAdd m j).isLt
  simp only [id] at hcell ⊢
  have hget :=
    congrArg
      (fun t : Tensor α [m + n] =>
        id (α := Tensor α []) (t[(Fin.natAdd m j : ℕ)]'hj))
      hrow
  simp only [id, Nat.add_sub_cancel_left] at hget
  simpa [GetElem.getElem, Fin.val_natAdd] using hget.trans hcell


/--
Determinant of a block-lower-triangular tensor:
`det [A 0; C B] = det A * det B`.
-/
@[main]
private lemma main
  [CommRing α]
  {m n : ℕ}
-- given
  (A : Tensor α [m, m])
  (B : Tensor α [n, n])
  (C : Tensor α [n, m]) :
-- imply
  id (α := Tensor α []) (A.hstack (0 : Tensor α [m, n]) ++ C.hstack B).det =
    id (α := Tensor α []) A.det * id (α := Tensor α []) B.det := by
-- proof
  let T := A.hstack (0 : Tensor α [m, n]) ++ C.hstack B
  apply Eq.trans (congrArg (id (α := Tensor α [])) (Det.eq.DetToMatrix T))
  have hT :
      T.toMatrix =
        (reindex finSumFinEquiv finSumFinEquiv
          (fromBlocks A.toMatrix 0 C.toMatrix B.toMatrix)) := by
    ext i j
    simp [T, Tensor.toMatrix, Matrix.reindex, Matrix.submatrix]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockLower_castAdd_castAdd A B C i j
      · simp [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
          fromBlocks_apply₁₂]
        simpa [GetElem.getElem, id] using get_blockLower_castAdd_natAdd A B C i j
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) j
      · simp [finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
          fromBlocks_apply₂₁, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockLower_natAdd_castAdd A B C i j
      · simp [finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₂₂, Tensor.toMatrix]
        simpa [GetElem.getElem, id] using get_blockLower_natAdd_natAdd A B C i j
  rw [hT, det_reindex_self, det_fromBlocks_zero₁₂]
  rw [← Det.eq.DetToMatrix A, ← Det.eq.DetToMatrix B]
  simp only [id]
  erw [Tensor.Mul]
  rfl


-- created on 2026-09-07
