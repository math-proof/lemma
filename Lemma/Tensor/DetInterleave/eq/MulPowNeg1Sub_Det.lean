import Lemma.Tensor.Delta.eq.Ite
import Lemma.Tensor.DetShiftMatrix.eq.PowNeg1Sub
import Lemma.Tensor.GetInterleave.eq.Delta_ToSplit
import Lemma.Tensor.EqMul1
import Lemma.Tensor.ToMatrixDot.eq.MulToMatrixS
open Matrix Tensor
set_option maxHeartbeats 800000


/--
Row index after left-multiplying by `ShiftMatrix(n, n/2, 1)`:
row `1` comes from row `n/2`, and rows `2..n/2` come from `1..n/2-1`.
Works for both even `n = 2d` (n/2 = d) and odd `n = 2d+1` (n/2 = d).
-/
private def Fin.shiftRow {n : ℕ} (i : Fin n) : Fin n :=
  if h : (i : ℕ) = 1 then
    ⟨n / 2, by
      have hin := i.isLt
      have h1 : 1 < n := by omega
      exact Nat.div_lt_self (by omega : 0 < n) (by decide : 1 < 2)⟩
  else if 1 < (i : ℕ) ∧ (i : ℕ) ≤ n / 2 then
    ⟨(i : ℕ) - 1, Nat.lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩
  else
    i


/--
Entry of `ShiftMatrix(n, n/2, 1)`: row `i` is sent to `i.shiftRow`.
Works for both even `n = 2d` (n/2 = d) and odd `n = 2d+1` (n/2 = d).
-/
private lemma get_shiftRow
    (n : ℕ) (hd : 1 < n / 2) (i j : Fin n) :
    (ShiftMatrix (α := ℝ) n (n / 2) 1).toMatrix i j =
      (↑(KroneckerDelta (i.shiftRow : ℕ) (j : ℕ)) : Tensor ℝ []) := by
  have hS := GetShiftMatrix.eq.Ite (α := ℝ) n (n / 2) 1 i j
  simp only [Tensor.toMatrix] at hS ⊢
  rw [hS]
  have hne : n / 2 ≠ 1 := by omega
  have hlt : ¬n / 2 < 1 := by omega
  simp only [hne, hlt, ↓reduceIte]
  have hδij : KroneckerDelta i j = KroneckerDelta (i : ℕ) (j : ℕ) := by
    simp [KroneckerDelta, Fin.ext_iff]
  rw [hδij]
  simp [Delta.eq.Ite]
  if hj0 : (j : ℕ) = n / 2 then
    simp [hj0]
    if hi1 : (i : ℕ) = 1 then
      have hσ : (i.shiftRow : ℕ) = n / 2 := by
        simp [Fin.shiftRow, hi1]
      simp [hi1, hσ]
    else
      simp [hi1]
      if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ n / 2 then
        have hσ : (i.shiftRow : ℕ) = (i : ℕ) - 1 := by
          simp [Fin.shiftRow, hi1, hmid]
        have : (i : ℕ) - 1 ≠ n / 2 := by omega
        simp [hσ, this]
      else
        have hσ : i.shiftRow = i := by
          simp [Fin.shiftRow, hi1, hmid]
        have : (i : ℕ) ≠ n / 2 := by omega
        simp [hσ, this]
  else
    simp [hj0]
    if hjm : 1 ≤ (j : ℕ) ∧ (j : ℕ) < n / 2 then
      simp [hjm]
      if hi1 : (i : ℕ) = 1 then
        have hσ : (i.shiftRow : ℕ) = n / 2 := by
          simp [Fin.shiftRow, hi1]
        have hR : n / 2 ≠ (j : ℕ) := by omega
        simp [hi1, hσ, hR]
        omega
      else
        if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ n / 2 then
          have hσ : (i.shiftRow : ℕ) = (i : ℕ) - 1 := by
            simp [Fin.shiftRow, hi1, hmid]
          have hiff : (i : ℕ) = (j : ℕ) + 1 ↔ (i : ℕ) - 1 = (j : ℕ) := by
            constructor <;> intro <;> omega
          simp [hσ]
          if hL : (i : ℕ) = (j : ℕ) + 1 then
            simp [hL]
          else
            simp [hL]
            intro; omega
        else
          have hσ : i.shiftRow = i := by
            simp [Fin.shiftRow, hi1, hmid]
          have hL : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
          have hR : (i : ℕ) ≠ (j : ℕ) := by omega
          simp [hσ, hL, hR]
    else
      simp [hjm]
      if hi1 : (i : ℕ) = 1 then
        have hσ : (i.shiftRow : ℕ) = n / 2 := by
          simp [Fin.shiftRow, hi1]
        have hL : (1 : ℕ) ≠ (j : ℕ) := by omega
        have hR : n / 2 ≠ (j : ℕ) := by omega
        simp [hi1, hσ, hL, hR]
      else
        if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ n / 2 then
          have hσ : (i.shiftRow : ℕ) = (i : ℕ) - 1 := by
            simp [Fin.shiftRow, hi1, hmid]
          have hL : (i : ℕ) ≠ (j : ℕ) := by omega
          have hR : (i : ℕ) - 1 ≠ (j : ℕ) := by omega
          simp [hσ, hL, hR]
        else
          have hσ : i.shiftRow = i := by
            simp [Fin.shiftRow, hi1, hmid]
          simp [hσ]


private lemma get_shift_mul
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d)) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j =
      (interleave d).toMatrix (i.shiftRow) j := by
  have hhalf : (d + d) / 2 = d := by
    have h : d + d = 2 * d := (two_mul d).symm
    rw [h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [ToMatrixDot.eq.MulToMatrixS, Matrix.mul_apply]
  have hSR (k : Fin (d + d)) :
      (ShiftMatrix (α := ℝ) (d + d) d 1).toMatrix i k =
        (↑(KroneckerDelta (i.shiftRow : ℕ) (k : ℕ)) : Tensor ℝ []) := by
    have h' := get_shiftRow (n := d + d) (by rw [hhalf]; omega) i k
    rw [hhalf] at h'
    exact h'
  have hterm (k : Fin (d + d)) :
      @HMul.hMul (Tensor ℝ []) (Tensor ℝ []) (Tensor ℝ []) instHMul
          ((ShiftMatrix (α := ℝ) (d + d) d 1).toMatrix i k)
          ((interleave d).toMatrix k j) =
        if k = i.shiftRow then
          (interleave d).toMatrix (i.shiftRow) j
        else
          (0 : Tensor ℝ []) := by
    rw [hSR k, Nat.Delta.eq.Ite]
    if hk : (i.shiftRow : ℕ) = (k : ℕ) then
      have hk' : k = i.shiftRow := Fin.ext hk.symm
      simp [hk, hk']
      erw [Nat.cast_one]
      exact one_mul ((interleave d).toMatrix (i.shiftRow) j)
    else
      have hk' : k ≠ i.shiftRow := fun h => hk (by rw [h])
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
  have hdiv : (d + d) / 2 = d := by
    have h : d + d = 2 * d := (two_mul d).symm
    rw [h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, Delta.eq.Ite]
  simp only [Fin.toSplit]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  obtain hi0 | hi1 := hi01 <;> obtain hj0 | hj1 := hj01
  · have hσ : (i.shiftRow : ℕ) = 0 := by simp [Fin.shiftRow, hi0]
    simp [hσ, hi0, hj0]
  · have hσ : (i.shiftRow : ℕ) = 0 := by simp [Fin.shiftRow, hi0]
    have : (0 : ℕ) ≠ d := by omega
    simp [hσ, hi0, hj1, this]
  · have hσ : (i.shiftRow : ℕ) = d := by
      simp [Fin.shiftRow, hi1, hdiv]
    have : d ≠ 0 := by omega
    simp [hσ, hi1, hj0, this]
  · have hσ : (i.shiftRow : ℕ) = d := by
      simp [Fin.shiftRow, hi1, hdiv]
    simp [hσ, hi1, hj1]


private lemma entry_lt_ge
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : (i : ℕ) < 2) (hj : 2 ≤ (j : ℕ)) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j = 0 := by
  have hdiv : (d + d) / 2 = d := by
    have h : d + d = 2 * d := (two_mul d).symm
    rw [h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, Delta.eq.Ite]
  simp only [Fin.toSplit]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  obtain hi0 | hi1 := hi01
  · have hσ : (i.shiftRow : ℕ) = 0 := by simp [Fin.shiftRow, hi0]
    simp [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have : (0 : ℕ) ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    else
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      have : (0 : ℕ) ≠ (j : ℕ) / 2 + d := by omega
      simp [hjo, one_mul, this]
  · have hσ : (i.shiftRow : ℕ) = d := by
      simp [Fin.shiftRow, hi1, hdiv]
    simp [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have : d ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    else
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo, one_mul]
      intro; omega


private lemma entry_ge_lt
    (d : ℕ) (hd : 1 < d) (i j : Fin (d + d))
    (hi : 2 ≤ (i : ℕ)) (hj : (j : ℕ) < 2) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix i j = 0 := by
  have hdiv : (d + d) / 2 = d := by
    have h : d + d = 2 * d := (two_mul d).symm
    rw [h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [get_shift_mul d hd i j, get_interleave_toMatrix, Delta.eq.Ite]
  simp only [Fin.toSplit]
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d then
    have hmid' : 1 < (i : ℕ) ∧ (i : ℕ) ≤ (d + d) / 2 := by
      obtain ⟨h1, h2⟩ := hmid; exact ⟨h1, h2.trans (le_of_eq hdiv.symm)⟩
    have hσ : (i.shiftRow : ℕ) = (i : ℕ) - 1 := by
      have hne : (i : ℕ) ≠ 1 := by omega
      simp [Fin.shiftRow, hne, hmid']
    simp [hσ]
    obtain hj0 | hj1 := hj01
    · have : (i : ℕ) - 1 ≠ 0 := by omega
      simp [hj0, this]
    · have : (i : ℕ) - 1 ≠ d := by omega
      simp [hj1, this]
  else
    have hmid' : ¬(1 < (i : ℕ) ∧ (i : ℕ) ≤ (d + d) / 2) := by
      intro h; exact hmid ⟨h.1, h.2.trans (le_of_eq hdiv)⟩
    have hσ : i.shiftRow = i := by
      have hne : (i : ℕ) ≠ 1 := by omega
      simp [Fin.shiftRow, hne, hmid']
    simp [hσ]
    obtain hj0 | hj1 := hj01
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
  have hdiv : (d + d) / 2 = d := by
    have h : d + d = 2 * d := (two_mul d).symm
    rw [h, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]
  rw [get_shift_mul d hd i j]
  rw [get_interleave_toMatrix, get_interleave_toMatrix]
  simp [Delta.eq.Ite, Fin.toSplit]
  if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d then
    have hmid' : 1 < (i : ℕ) ∧ (i : ℕ) ≤ (d + d) / 2 := by
      obtain ⟨h1, h2⟩ := hmid; exact ⟨h1, h2.trans (le_of_eq hdiv.symm)⟩
    have hσ : (i.shiftRow : ℕ) = (i : ℕ) - 1 := by
      have hne : (i : ℕ) ≠ 1 := by omega
      simp [Fin.shiftRow, hne, hmid']
    rw [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have hje' : ((j : ℕ) - 2) % 2 = 0 := by omega
      simp [hje, hje']
      have hiff : ((i : ℕ) - 1 = (j : ℕ) / 2) ↔ ((i : ℕ) - 2 = ((j : ℕ) - 2) / 2) := by
        constructor <;> intro <;> omega
      simp [hiff]
    else
      have hje' : ((j : ℕ) - 2) % 2 = 1 := by omega
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo, hje']
      have hL : (i : ℕ) - 1 ≠ (j : ℕ) / 2 + d := by omega
      have hR : (i : ℕ) - 2 ≠ ((j : ℕ) - 2) / 2 + (d - 1) := by omega
      simp [hL, hR]
  else
    have hmid' : ¬(1 < (i : ℕ) ∧ (i : ℕ) ≤ (d + d) / 2) := by
      intro h; exact hmid ⟨h.1, h.2.trans (le_of_eq hdiv)⟩
    have hσ : i.shiftRow = i := by
      have hne : (i : ℕ) ≠ 1 := by omega
      simp [Fin.shiftRow, hne, hmid']
    rw [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have hje' : ((j : ℕ) - 2) % 2 = 0 := by omega
      simp [hje, hje']
      have hL : (i : ℕ) ≠ (j : ℕ) / 2 := by omega
      have hR : (i : ℕ) - 2 ≠ ((j : ℕ) - 2) / 2 := by omega
      simp [hL, hR]
    else
      have hje' : ((j : ℕ) - 2) % 2 = 1 := by omega
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
    | .inr i => ⟨(i : ℕ) + 2, by omega⟩
  invFun i :=
    if h : (i : ℕ) ≤ 1 then
      .inl ⟨i, Nat.lt_succ_of_le h⟩
    else
      .inr ⟨(i : ℕ) - 2, by omega⟩
  left_inv x := by
    match x with
    | .inl i =>
      have hi : (i : ℕ) ≤ 1 := Nat.le_of_lt_succ i.isLt
      simp [hi]
    | .inr i =>
      have hi : ¬((i : ℕ) + 2 ≤ 1) := by omega
      simp [hi]
  right_inv i := by
    if h : (i : ℕ) ≤ 1 then
      simp [h]
    else
      simp [h]
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
      Sum.inr ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩ := by
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
  if hi : (i : ℕ) < 2 then
    have hbi := blockEquiv_symm_lt d (by omega) i hi
    if hj : (j : ℕ) < 2 then
      have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, fromBlocks_apply₁₁, Matrix.one_apply, Fin.ext_iff, hi, hj]
    else
      have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, fromBlocks_apply₁₂, hi, hj]
  else
    have hbi := blockEquiv_symm_ge d (by omega) i (Nat.le_of_not_lt hi)
    if hj : (j : ℕ) < 2 then
      have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, fromBlocks_apply₂₁, hi, hj]
    else
      have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, fromBlocks_apply₂₂, hi, hj]


private lemma shift_mul_block
    (d : ℕ) (hd : 1 < d) :
    ((ShiftMatrix (α := ℝ) (d + d) d 1) @ (interleave d)).toMatrix =
      reindex (blockEquiv d (by omega)) (blockEquiv d (by omega))
        (fromBlocks (1 : Matrix (Fin 2) (Fin 2) (Tensor ℝ [])) 0 0
          (interleave (d - 1)).toMatrix) := by
  ext i j
  rw [reindex_fromBlocks_apply d hd i j]
  if hi : (i : ℕ) < 2 then
    if hj : (j : ℕ) < 2 then
      simp [hi, hj]
      exact entry_lt_lt d hd i j hi hj
    else
      simp [hi, hj]
      exact entry_lt_ge d hd i j hi (Nat.le_of_not_lt hj)
  else
    if hj : (j : ℕ) < 2 then
      simp [hi, hj]
      exact entry_ge_lt d hd i j (Nat.le_of_not_lt hi) hj
    else
      simp [hi, hj]
      exact entry_ge_ge d hd i j (Nat.le_of_not_lt hi) (Nat.le_of_not_lt hj)


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.DetInterleave.eq.MulPowNeg1Sub_Det |
-/
@[main]
private lemma main
-- given
  (d : ℕ) (hd : 1 < d) :
-- imply
  (interleave d).toMatrix.det =
    Mul.mul ((-1 : Tensor ℝ []) ^ (d - 1))
      (interleave (d - 1)).toMatrix.det := by
-- proof
  let S := ShiftMatrix (α := ℝ) (d + d) d 1
  let P := interleave d
  have hS : S.toMatrix.det = (-1 : Tensor ℝ []) ^ (d - 1) := by
    apply Eq.trans (Det.eq.DetToMatrix S).symm
    apply DetShiftMatrix.eq.PowNeg1Sub (α := ℝ) _ _ _ (by omega) hd
  have hSP : (S @ P).toMatrix.det = (interleave (d - 1)).toMatrix.det := by
    rw [shift_mul_block d hd, det_reindex_self, det_fromBlocks_zero₂₁, det_one,
      one_mul]
  have hprod : Mul.mul S.toMatrix.det P.toMatrix.det =
      (interleave (d - 1)).toMatrix.det :=
    (Matrix.det_mul S.toMatrix P.toMatrix).symm.trans
      ((ToMatrixDot.eq.MulToMatrixS S P) ▸ hSP)
  rw [hS] at hprod
  have mul1 (x : Tensor ℝ []) : Mul.mul (1 : Tensor ℝ []) x = x := by
    erw [← Tensor.Mul]
    apply EqMul1 _
  obtain he | ho := Nat.even_or_odd (d - 1)
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
      erw [Vector.GetMul.eq.MulGetS.fin, Vector.GetMul.eq.MulGetS.fin]
      simp [Neg.neg]
      rw [← _root_.mul_assoc]
      have ha : (((1 : Tensor ℝ []).data).map (fun y : ℝ => -y)).head = (-1 : ℝ) := by
        simp
        rfl
      erw [ha]
      norm_num
    calc _ = P.toMatrix.det := rfl
      _ = Mul.mul (-1) (Mul.mul (-1) P.toMatrix.det) := (hinv _).symm
      _ = Mul.mul (-1) (interleave (d - 1)).toMatrix.det := by
        rw [hprod]


-- created on 2026-09-11
