import Lemma.Tensor.DetShiftMatrix.eq.PowNeg1Sub
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.EqMul1
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
open Matrix Tensor
set_option maxHeartbeats 800000


/--
Row index after left-multiplying by `ShiftMatrix(2d, d, 1)`:
row `1` comes from row `d`, and rows `2..d` come from `1..d-1`.
-/
private def shiftRow (d : ℕ) (i : Fin (d + d)) : Fin (d + d) :=
  if h : (i : ℕ) = 1 then
    ⟨d, by have := i.isLt; omega⟩
  else if 1 < (i : ℕ) ∧ (i : ℕ) ≤ d then
    ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  else
    i


private lemma cast_delta (a b : ℕ) :
    (↑(KroneckerDelta a b) : Tensor ℝ []) =
      if a = b then (1 : Tensor ℝ []) else (0 : Tensor ℝ []) := by
  rw [Nat.Delta.eq.Ite]
  split_ifs
  · exact Nat.cast_one
  · exact Nat.cast_zero


private lemma toSplit_val {d : ℕ} (j : Fin (d + d)) :
    (j.toSplit : ℕ) = (j : ℕ) / 2 + (j : ℕ) % 2 * d :=
  rfl


private lemma get_shiftRow
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d)) :
    (ShiftMatrix (α := ℝ) (d + d) d 1).toMatrix i j =
      (↑(KroneckerDelta (shiftRow d i : ℕ) (j : ℕ)) : Tensor ℝ []) := by
  have hS := GetShiftMatrix.eq.Ite (α := ℝ) (d + d) d 1 i j
  simp only [Tensor.toMatrix] at hS ⊢
  rw [hS]
  have hne : d ≠ 1 := by omega
  have hlt : ¬d < 1 := by omega
  simp only [hne, hlt, ↓reduceIte]
  have hδij : KroneckerDelta i j = KroneckerDelta (i : ℕ) (j : ℕ) := by
    simp [KroneckerDelta, Fin.ext_iff]
  rw [hδij]
  rw [cast_delta, cast_delta, cast_delta, cast_delta]
  by_cases hj0 : (j : ℕ) = d
  · simp [hj0]
    by_cases hi1 : (i : ℕ) = 1
    · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
      simp [hi1, hσ]
    · simp [hi1]
      by_cases hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d
      · have hσ : (shiftRow d i : ℕ) = (i : ℕ) - 1 := by
          simp [shiftRow, hi1, hmid]
        have : (i : ℕ) - 1 ≠ d := by omega
        simp [hσ, this]
      · have hσ : shiftRow d i = i := by simp [shiftRow, hi1, hmid]
        have : (i : ℕ) ≠ d := by omega
        simp [hσ, this]
  · simp [hj0]
    by_cases hjm : 1 ≤ (j : ℕ) ∧ (j : ℕ) < d
    · simp [hjm]
      by_cases hi1 : (i : ℕ) = 1
      · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
        have hR : d ≠ (j : ℕ) := by omega
        simp [hi1, hσ, hR]
        intro; omega
      · by_cases hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d
        · have hσ : (shiftRow d i : ℕ) = (i : ℕ) - 1 := by
            simp [shiftRow, hi1, hmid]
          have hiff : (i : ℕ) = (j : ℕ) + 1 ↔ (i : ℕ) - 1 = (j : ℕ) := by
            constructor <;> intro <;> omega
          simp [hσ]
          by_cases hL : (i : ℕ) = (j : ℕ) + 1
          · simp [hL]
          · simp [hL]
            intro; omega
        · have hσ : shiftRow d i = i := by simp [shiftRow, hi1, hmid]
          have hL : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
          have hR : (i : ℕ) ≠ (j : ℕ) := by omega
          simp [hσ, hL, hR]
    · simp [hjm]
      by_cases hi1 : (i : ℕ) = 1
      · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
        have hL : (1 : ℕ) ≠ (j : ℕ) := by omega
        have hR : d ≠ (j : ℕ) := by omega
        simp [hi1, hσ, hL, hR]
      · by_cases hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d
        · have hσ : (shiftRow d i : ℕ) = (i : ℕ) - 1 := by
            simp [shiftRow, hi1, hmid]
          have hL : (i : ℕ) ≠ (j : ℕ) := by omega
          have hR : (i : ℕ) - 1 ≠ (j : ℕ) := by omega
          simp [hσ, hL, hR]
        · have hσ : shiftRow d i = i := by simp [shiftRow, hi1, hmid]
          simp [hσ]


private lemma get_shift_mul
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d)) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j =
      (interleave d).toMatrix (shiftRow d i) j := by
  rw [ToMatrixDot.eq.MulToMatrixS, Matrix.mul_apply]
  have hterm (k : Fin (d + d)) :
      @HMul.hMul (Tensor ℝ []) (Tensor ℝ []) (Tensor ℝ []) instHMul
          ((ShiftMatrix (α := ℝ) (d + d) d 1).toMatrix i k)
          ((interleave d).toMatrix k j) =
        if k = shiftRow d i then
          (interleave d).toMatrix (shiftRow d i) j
        else
          (0 : Tensor ℝ []) := by
    rw [get_shiftRow d hd i k, Nat.Delta.eq.Ite]
    by_cases hk : (shiftRow d i : ℕ) = (k : ℕ)
    · have hk' : k = shiftRow d i := Fin.ext hk.symm
      simp [hk, hk']
      erw [Nat.cast_one]
      exact one_mul ((interleave d).toMatrix (shiftRow d i) j)
    · have hk' : k ≠ shiftRow d i := fun h => hk (by rw [h])
      simp [hk, hk']
      erw [Nat.cast_zero]
      exact zero_mul ((interleave d).toMatrix k j)
  change ∑ k ∈ Finset.univ,
      @HMul.hMul (Tensor ℝ []) (Tensor ℝ []) (Tensor ℝ []) instHMul
        ((ShiftMatrix (α := ℝ) (d + d) d 1).toMatrix i k)
        ((interleave d).toMatrix k j) = _
  rw [Finset.sum_congr rfl fun k _ => hterm k]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]


private lemma get_interleave_toMatrix
    (d : ℕ) (k j : Fin (d + d)) :
    (interleave d).toMatrix k j =
      (↑(KroneckerDelta (k : ℕ) (j.toSplit : ℕ)) : Tensor ℝ []) := by
  have h := GetInterleave.eq.Delta_ToSplit k j
  simp only [Tensor.toMatrix, GetElem.getElem] at h ⊢
  exact h


private lemma entry_lt_lt
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : (i : ℕ) < 2) (hj : (j : ℕ) < 2) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j =
      if (i : ℕ) = (j : ℕ) then (1 : Tensor ℝ []) else 0 := by
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, cast_delta, toSplit_val]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  rcases hi01 with hi0 | hi1 <;> rcases hj01 with hj0 | hj1
  · have hσ : (shiftRow d i : ℕ) = 0 := by simp [shiftRow, hi0]
    simp [hσ, hi0, hj0]
  · have hσ : (shiftRow d i : ℕ) = 0 := by simp [shiftRow, hi0]
    have : (0 : ℕ) ≠ d := by omega
    simp [hσ, hi0, hj1, this]
  · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
    have : d ≠ 0 := by omega
    simp [hσ, hi1, hj0, this]
  · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
    simp [hσ, hi1, hj1]


private lemma entry_lt_ge
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : (i : ℕ) < 2) (hj : 2 ≤ (j : ℕ)) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j = 0 := by
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, cast_delta, toSplit_val]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  rcases hi01 with hi0 | hi1
  · have hσ : (shiftRow d i : ℕ) = 0 := by simp [shiftRow, hi0]
    simp [hσ]
    by_cases hje : (j : ℕ) % 2 = 0
    · have : (0 : ℕ) ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    · have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      have : (0 : ℕ) ≠ (j : ℕ) / 2 + d := by omega
      simp [hjo, one_mul, this]
  · have hσ : (shiftRow d i : ℕ) = d := by simp [shiftRow, hi1]
    simp [hσ]
    by_cases hje : (j : ℕ) % 2 = 0
    · have : d ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    · have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo, one_mul]
      intro; omega


private lemma entry_ge_lt
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j = 0 := by
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, cast_delta, toSplit_val]
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  by_cases hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d
  · have hσ : (shiftRow d i : ℕ) = (i : ℕ) - 1 := by
      simp [shiftRow, hmid, show (i : ℕ) ≠ 1 by omega]
    simp [hσ]
    rcases hj01 with hj0 | hj1
    · have : (i : ℕ) - 1 ≠ 0 := by omega
      simp [hj0, this]
    · have : (i : ℕ) - 1 ≠ d := by omega
      simp [hj1, this]
  · have hσ : shiftRow d i = i := by
      simp [shiftRow, hmid, show (i : ℕ) ≠ 1 by omega]
    simp [hσ]
    rcases hj01 with hj0 | hj1
    · have : (i : ℕ) ≠ 0 := by omega
      simp [hj0, this]
    · have : (i : ℕ) ≠ d := by omega
      simp [hj1, this]


private lemma entry_ge_ge
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : 2 ≤ (i : ℕ)) (hj : 2 ≤ (j : ℕ)) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j =
      (interleave (d - 1)).toMatrix
        ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩
        ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩ := by
  rw [get_shift_mul d hd i j]
  rw [get_interleave_toMatrix, get_interleave_toMatrix]
  rw [cast_delta, cast_delta]
  rw [toSplit_val, toSplit_val]
  by_cases hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d
  · have hσ : (shiftRow d i : ℕ) = (i : ℕ) - 1 := by
      simp [shiftRow, hmid, show (i : ℕ) ≠ 1 by omega]
    rw [hσ]
    by_cases hje : (j : ℕ) % 2 = 0
    · have hje' : ((j : ℕ) - 2) % 2 = 0 := by omega
      simp [hje, hje']
      have hiff : ((i : ℕ) - 1 = (j : ℕ) / 2) ↔ ((i : ℕ) - 2 = ((j : ℕ) - 2) / 2) := by
        constructor <;> intro <;> omega
      simp [hiff]
    · have hje' : ((j : ℕ) - 2) % 2 = 1 := by omega
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo, hje']
      have hL : (i : ℕ) - 1 ≠ (j : ℕ) / 2 + d := by omega
      have hR : (i : ℕ) - 2 ≠ ((j : ℕ) - 2) / 2 + (d - 1) := by omega
      simp [hL, hR]
  · have hσ : shiftRow d i = i := by
      simp [shiftRow, hmid, show (i : ℕ) ≠ 1 by omega]
    rw [hσ]
    by_cases hje : (j : ℕ) % 2 = 0
    · have hje' : ((j : ℕ) - 2) % 2 = 0 := by omega
      simp [hje, hje']
      have hL : (i : ℕ) ≠ (j : ℕ) / 2 := by omega
      have hR : (i : ℕ) - 2 ≠ ((j : ℕ) - 2) / 2 := by omega
      simp [hL, hR]
    · have hje' : ((j : ℕ) - 2) % 2 = 1 := by omega
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo, hje']
      have hiff :
          ((i : ℕ) = (j : ℕ) / 2 + d) ↔
            ((i : ℕ) - 2 = ((j : ℕ) - 2) / 2 + (d - 1)) := by
        constructor <;> intro <;> omega
      simp [hiff]


private lemma block_dim (d : ℕ) (hd : 0 < d) :
    2 + ((d - 1) + (d - 1)) = d + d := by
  omega


/--
Equiv identifying the leading `2` and trailing `2(d-1)` blocks with `Fin (d+d)`.
-/
private def blockEquiv (d : ℕ) (hd : 0 < d) :
    Equiv (Sum (Fin 2) (Fin ((d - 1) + (d - 1)))) (Fin (d + d)) where
  toFun x :=
    match x with
    | .inl i => ⟨(i : ℕ), Nat.lt_of_lt_of_le i.isLt (by omega : (2 : ℕ) ≤ d + d)⟩
    | .inr i => ⟨(i : ℕ) + 2, by
        have := i.isLt
        have := block_dim d hd
        omega⟩
  invFun i :=
    if h : (i : ℕ) ≤ 1 then
      .inl ⟨i, Nat.lt_succ_of_le h⟩
    else
      .inr ⟨(i : ℕ) - 2, by
        have := i.isLt
        have := block_dim d hd
        omega⟩
  left_inv x := by
    match x with
    | .inl i =>
      have hi : (i : ℕ) ≤ 1 := Nat.le_of_lt_succ i.isLt
      simp [hi]
    | .inr i =>
      have hi : ¬((i : ℕ) + 2 ≤ 1) := by omega
      simp [hi]
  right_inv i := by
    by_cases h : (i : ℕ) ≤ 1
    · simp [h]
    · simp [h]
      apply Fin.ext
      simp
      omega


private lemma blockEquiv_symm_lt
    (d : ℕ) (hd : 0 < d) (i : Fin (d + d)) (hi : (i : ℕ) < 2) :
    (blockEquiv d hd).symm i = Sum.inl ⟨i, hi⟩ := by
  have h : (i : ℕ) ≤ 1 := Nat.le_of_lt_succ hi
  simp [blockEquiv, Equiv.symm, h]


private lemma blockEquiv_symm_ge
    (d : ℕ) (hd : 0 < d) (i : Fin (d + d)) (hi : 2 ≤ (i : ℕ)) :
    (blockEquiv d hd).symm i =
      Sum.inr ⟨(i : ℕ) - 2, by have := i.isLt; have := block_dim d hd; omega⟩ := by
  have h : ¬(i : ℕ) ≤ 1 := by omega
  simp [blockEquiv, Equiv.symm, h]


private lemma reindex_fromBlocks_apply
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d)) :
    (reindex (blockEquiv d (by omega)) (blockEquiv d (by omega))
        (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (Tensor ℝ [])) 0 0
          (interleave (d - 1)).toMatrix)) i j =
      if hi : (i : ℕ) < 2 then
        if _hj : (j : ℕ) < 2 then
          if (i : ℕ) = (j : ℕ) then (1 : Tensor ℝ []) else 0
        else
          0
      else
        if _hj : (j : ℕ) < 2 then
          0
        else
          (interleave (d - 1)).toMatrix
            ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩
            ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩ := by
  simp only [Matrix.reindex, Matrix.submatrix]
  by_cases hi : (i : ℕ) < 2
  · have hbi := blockEquiv_symm_lt d (by omega) i hi
    by_cases hj : (j : ℕ) < 2
    · have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, fromBlocks_apply₁₁, Matrix.one_apply, Fin.ext_iff, hi, hj]
    · have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, fromBlocks_apply₁₂, hi, hj]
  · have hbi := blockEquiv_symm_ge d (by omega) i (Nat.le_of_not_lt hi)
    by_cases hj : (j : ℕ) < 2
    · have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, fromBlocks_apply₂₁, hi, hj]
    · have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, fromBlocks_apply₂₂, hi, hj]


private lemma shift_mul_block
    (d : ℕ) (hd : 1 < d) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix =
      reindex (blockEquiv d (by omega)) (blockEquiv d (by omega))
        (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (Tensor ℝ [])) 0 0
          (interleave (d - 1)).toMatrix) := by
  ext i j
  rw [reindex_fromBlocks_apply d hd i j]
  by_cases hi : (i : ℕ) < 2
  · by_cases hj : (j : ℕ) < 2
    · simp [hi, hj]
      exact entry_lt_lt d hd i j hi hj
    · simp [hi, hj]
      exact entry_lt_ge d hd i j hi (Nat.le_of_not_lt hj)
  · by_cases hj : (j : ℕ) < 2
    · simp [hi, hj]
      exact entry_ge_lt d hd i j (Nat.le_of_not_lt hi) hj
    · simp [hi, hj]
      exact entry_ge_ge d hd i j (Nat.le_of_not_lt hi) (Nat.le_of_not_lt hj)


private lemma det_rec
    (d : ℕ) (hd : 1 < d) :
    (interleave d).toMatrix.det =
      Mul.mul ((-1 : Tensor ℝ []) ^ (d - 1))
        (interleave (d - 1)).toMatrix.det := by
  let S := ShiftMatrix (α := ℝ) (d + d) d 1
  let P := interleave d
  have hmul := Matrix.det_mul S.toMatrix P.toMatrix
  have hdot : (S @ P).toMatrix = S.toMatrix * P.toMatrix :=
    ToMatrixDot.eq.MulToMatrixS S P
  have hS : S.toMatrix.det = (-1 : Tensor ℝ []) ^ (d - 1) := by
    apply Eq.trans (Det.eq.DetToMatrix S).symm
    exact DetShiftMatrix.eq.PowNeg1Sub (α := ℝ) (d + d) d 1 (by omega) hd
  have hSP : (S @ P).toMatrix.det = (interleave (d - 1)).toMatrix.det := by
    rw [shift_mul_block d hd, det_reindex_self, det_fromBlocks_zero₂₁, det_one,
      one_mul]
  have hprod : Mul.mul S.toMatrix.det P.toMatrix.det =
      (interleave (d - 1)).toMatrix.det :=
    hmul.symm.trans (hdot ▸ hSP)
  rw [hS] at hprod
  have mul1 (x : Tensor ℝ []) : Mul.mul (1 : Tensor ℝ []) x = x := by
    erw [← Tensor.Mul]
    exact EqMul1 x
  rcases Nat.even_or_odd (d - 1) with he | ho
  · have hs : (-1 : Tensor ℝ []) ^ (d - 1) = 1 := Even.neg_one_pow he
    simp [hs] at hprod ⊢
    rw [mul1] at hprod ⊢
    simpa [P] using hprod
  · have hs : (-1 : Tensor ℝ []) ^ (d - 1) = -1 := Odd.neg_one_pow ho
    simp [hs] at hprod ⊢
    have hinv (x : Tensor ℝ []) :
        Mul.mul (-1 : Tensor ℝ []) (Mul.mul (-1) x) = x := by
      apply Eq.of.EqDataS
      ext i
      fin_cases i
      simp [Mul.mul]
      rw [Vector.Head.eq.Get_0.fin]
      erw [Vector.GetMul.eq.MulGetS.fin]
      erw [Vector.GetMul.eq.MulGetS.fin]
      simp [Neg.neg]
      rw [← _root_.mul_assoc]
      have ha : (((1 : Tensor ℝ []).data).map (fun y : ℝ => -y)).head = (-1 : ℝ) := by
        simp
        rfl
      erw [ha]
      norm_num
    calc
      (interleave d).toMatrix.det
          = P.toMatrix.det := rfl
      _ = Mul.mul (-1) (Mul.mul (-1) P.toMatrix.det) := (hinv _).symm
      _ = Mul.mul (-1) (interleave (d - 1)).toMatrix.det := by
            rw [hprod]


private lemma pow_neg_one_step (d : ℕ) (hd : 1 < d) :
    Mul.mul ((-1 : Tensor ℝ []) ^ (d - 1)) ((-1 : Tensor ℝ []) ^ ((d - 1) / 2)) =
      (-1 : Tensor ℝ []) ^ (d / 2) := by
  rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [hk]
    have hk0 : 0 < k := by omega
    have h2 : k + k = 2 * k := (two_mul k).symm
    simp [h2]
    have hodd : Odd (2 * k - 1) := ⟨k - 1, by omega⟩
    have hs : (-1 : Tensor ℝ []) ^ (2 * k - 1) = -1 := Odd.neg_one_pow hodd
    have hdiv : (2 * k - 1) / 2 = k - 1 := by omega
    rw [hs, hdiv]
    rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
    · have hkm : Odd (k - 1) := ⟨m - 1, by omega⟩
      have h1 : (-1 : Tensor ℝ []) ^ (k - 1) = -1 := Odd.neg_one_pow hkm
      have h2' : (-1 : Tensor ℝ []) ^ k = 1 := Even.neg_one_pow ⟨m, hm⟩
      simp [h1, h2']
      exact (neg_mul_neg (1 : Tensor ℝ []) 1).trans (one_mul 1)
    · have hkm : Even (k - 1) := ⟨m, by omega⟩
      have h1 : (-1 : Tensor ℝ []) ^ (k - 1) = 1 := Even.neg_one_pow hkm
      have h2' : (-1 : Tensor ℝ []) ^ k = -1 := Odd.neg_one_pow ⟨m, hm⟩
      simp [h1, h2']
      exact mul_one (-1 : Tensor ℝ [])
  · rw [hk]
    have he : Even (2 * k) := even_two_mul k
    have hs : (-1 : Tensor ℝ []) ^ (2 * k + 1 - 1) = 1 := by
      change (-1 : Tensor ℝ []) ^ (2 * k) = 1
      exact Even.neg_one_pow he
    have hdiv : (2 * k + 1 - 1) / 2 = k := by omega
    have hgoal : (2 * k + 1) / 2 = k := by omega
    rw [hs, hdiv, hgoal]
    exact one_mul _


/--
Even/odd gather \(\boldsymbol{P}=\mathrm{interleave}\,d\) has determinant
\(\det\boldsymbol{P}=(-1)^{d/2}\) (Nat floor division).

Proof plan (row shift / induction): left-multiply by `ShiftMatrix(2d, d, 1)`
moves row `d` to index `1` with sign `(-1)^(d-1)`; the leading `2×2` is `I`
and the trailing block is `interleave (d-1)`, so
`det P_d = (-1)^(d-1) · det P_{d-1}`.
-/
@[main]
private lemma main
  {d : ℕ} :
-- imply
  (interleave d).det = (-1) ^ (d / 2) := by
-- proof
  induction d with
  | zero =>
    apply Eq.trans (Det.eq.DetToMatrix (interleave 0))
    rw [Matrix.det_fin_zero]
    rfl
  | succ d ih =>
    cases d with
    | zero =>
      apply Eq.trans (Det.eq.DetToMatrix (interleave 1))
      have hP : (interleave 1).toMatrix = (1 : Matrix (Fin 2) (Fin 2) (Tensor ℝ [])) := by
        ext i j
        rw [get_interleave_toMatrix, cast_delta, toSplit_val, Matrix.one_apply]
        have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by
          have := i.isLt
          omega
        have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by
          have := j.isLt
          omega
        rcases hi01 with hi0 | hi1 <;> rcases hj01 with hj0 | hj1
        · simp [hi0, hj0, Fin.ext_iff]
        · simp [hi0, hj1, Fin.ext_iff]
        · simp [hi1, hj0, Fin.ext_iff]
        · simp [hi1, hj1, Fin.ext_iff]
      rw [hP, det_one]
      rfl
    | succ n =>
      have hd : 1 < n + 2 := by omega
      apply Eq.trans (Det.eq.DetToMatrix (interleave (n + 2)))
      have hrec := det_rec (n + 2) hd
      have hdim : n + 2 - 1 = n + 1 := Nat.add_sub_cancel (n + 1) 1
      simp [hdim] at hrec
      rw [hrec]
      have ih' : (interleave (n + 1)).toMatrix.det = (-1) ^ ((n + 1) / 2) :=
        (Det.eq.DetToMatrix (interleave (n + 1))).symm.trans ih
      rw [ih']
      exact pow_neg_one_step (n + 2) hd


-- created on 2026-09-07
-- updated on 2026-09-11
