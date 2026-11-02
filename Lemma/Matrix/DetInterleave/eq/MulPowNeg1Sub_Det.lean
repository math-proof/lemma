import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Matrix.Basic
import Def.LinearAlgebra.Matrix.Interleave
import Lemma.Matrix.GetShiftMatrix.eq.DeltaShiftRow
import Lemma.Matrix.DetShiftMatrix.eq.PowNeg1Sub
import Lemma.Fin.ShiftRow.eq.Ite
import Lemma.Fin.ToSplit.eq.Ite_Div_2
import Lemma.Fin.OfSplit.eq.Ite_Mul2
import Lemma.Nat.Delta_OfSplit.eq.Delta_ToSplit
import Lemma.Nat.Delta.eq.Ite
open Matrix Nat Fin



private lemma get_interleave
  (d : ℕ)
  (k j : Fin (d + d)) :
    interleave d k j =
      (KroneckerDelta (k : ℕ) (j.toSplit : ℕ) : ℝ) := by
  have hof :
    interleave d k j = (KroneckerDelta (j : ℕ) (k.ofSplit : ℕ) : ℝ) := by
    simp only [interleave, Matrix.of_apply, OfSplit.eq.Ite_Mul2]
    split_ifs <;> rfl
  rw [hof]
  exact congrArg (fun n : ℕ => (n : ℝ)) (Delta_OfSplit.eq.Delta_ToSplit k j)

private lemma get_shift_mul
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d)) :
    ((shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d) i j =
      interleave d (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩) j := by
  simp only [Matrix.mul_apply, GetShiftMatrix.eq.DeltaShiftRow]
  have hterm (k : Fin (d + d)) :
    (KroneckerDelta (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩) k : ℝ) *
        interleave d k j =
      if k = i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ then
        interleave d (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩) j
      else
        0 := by
    rw [Delta.eq.Ite]
    if hk : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = (k : ℕ) then
      have hk' : k = i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ := Fin.ext hk.symm
      simp [hk', Nat.cast_one]
    else
      have hk' : k ≠ i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ := fun h => hk (by rw [h])
      simp [hk']
      intro h
      exact (hk' h.symm).elim
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  simp [Finset.mem_univ]


-- Entry lemmas for the block decomposition (ported from Tensor)
private lemma entry_lt_lt
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d))
  (hi : (i : ℕ) < 2)
  (hj : (j : ℕ) < 2) :
    ((shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d) i j =
      if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0 := by
  rw [get_shift_mul d hd i j, get_interleave, Delta.eq.Ite]
  simp only [ToSplit.eq.Ite_Div_2]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  obtain hi0 | hi1 := hi01
  ·
    obtain hj0 | hj1 := hj01
    ·
      have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = 0 := by
        rw [ShiftRow.eq.Ite]
        simp [hi0]
        omega
      simp [hσ, hi0, hj0]
    ·
      have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = 0 := by
        rw [ShiftRow.eq.Ite]
        simp [hi0]
        omega
      have : (0 : ℕ) ≠ d := by omega
      simp [hσ, hi0, hj1, this]
  ·
    obtain hj0 | hj1 := hj01
    ·
      have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = d := by
        rw [ShiftRow.eq.Ite]
        simp [hi1]
      have : d ≠ 0 := by omega
      simp [hσ, hi1, hj0, this]
    ·
      have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = d := by
        rw [ShiftRow.eq.Ite]
        simp [hi1]
      simp [hσ, hi1, hj1]

private lemma entry_lt_ge
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d))
  (hi : (i : ℕ) < 2)
  (hj : 2 ≤ (j : ℕ)) :
    ((shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d) i j = 0 := by
  rw [get_shift_mul d hd i j, get_interleave, Delta.eq.Ite]
  simp only [ToSplit.eq.Ite_Div_2]
  have hi01 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
  obtain hi0 | hi1 := hi01
  ·
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = 0 := by
      rw [ShiftRow.eq.Ite]
      simp [hi0]
      omega
    simp [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have : (0 : ℕ) ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    else
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      have : (0 : ℕ) ≠ (j : ℕ) / 2 + d := by omega
      simp [hjo, this]
  ·
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = d := by
      rw [ShiftRow.eq.Ite]
      simp [hi1]
    simp [hσ]
    if hje : (j : ℕ) % 2 = 0 then
      have : d ≠ (j : ℕ) / 2 := by omega
      simp [hje, this]
    else
      have hjo : (j : ℕ) % 2 = 1 := Nat.mod_two_ne_zero.mp hje
      simp [hjo]
      omega

private lemma entry_ge_lt
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d))
  (hi : 2 ≤ (i : ℕ))
  (hj : (j : ℕ) < 2) :
    ((shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d) i j = 0 := by
  rw [get_shift_mul d hd i j, get_interleave, Delta.eq.Ite]
  simp only [ToSplit.eq.Ite_Div_2]
  have hj01 : (j : ℕ) = 0 ∨ (j : ℕ) = 1 := by omega
  if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d then
    have hne : (i : ℕ) ≠ 1 := by omega
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = (i : ℕ) - 1 := by
      rw [ShiftRow.eq.Ite]
      simp [hne, hmid]
    simp [hσ]
    obtain hj0 | hj1 := hj01
    ·
      have : (i : ℕ) - 1 ≠ 0 := by omega
      simp [hj0, this]
    ·
      have : (i : ℕ) - 1 ≠ d := by omega
      simp [hj1, this]
  else
    have hne : (i : ℕ) ≠ 1 := by omega
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = (i : ℕ) := by
      rw [ShiftRow.eq.Ite]
      simp [hne, hmid]
      omega
    simp [hσ]
    obtain hj0 | hj1 := hj01
    ·
      have : (i : ℕ) ≠ 0 := by omega
      simp [hj0, this]
    ·
      have : (i : ℕ) ≠ d := by omega
      simp [hj1, this]

private lemma entry_ge_ge
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d))
  (hi : 2 ≤ (i : ℕ))
  (hj : 2 ≤ (j : ℕ)) :
    ((shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d) i j =
      interleave (d - 1)
        ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩
        ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩ := by
  rw [get_shift_mul d hd i j]
  rw [get_interleave, get_interleave]
  simp [Delta.eq.Ite, ToSplit.eq.Ite_Div_2]
  if hmid : 1 < (i : ℕ) ∧ (i : ℕ) ≤ d then
    have hne : (i : ℕ) ≠ 1 := by omega
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = (i : ℕ) - 1 := by
      rw [ShiftRow.eq.Ite]
      simp [hne, hmid]
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
    have hne : (i : ℕ) ≠ 1 := by omega
    have hσ : (i.shiftRow ⟨d, by omega⟩ ⟨1, by omega⟩ : ℕ) = (i : ℕ) := by
      rw [ShiftRow.eq.Ite]
      simp [hne, hmid]
      omega
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

/-- Equiv identifying the leading `2` and trailing `2(d-1)` blocks with `Fin (d+d)`. -/
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
  (d : ℕ)
  (hd : 0 < d)
  (i : Fin (d + d))
  (hi : (i : ℕ) < 2) :
    (blockEquiv d hd).symm i = Sum.inl ⟨i, hi⟩ := by
  have h : (i : ℕ) ≤ 1 := Nat.le_of_lt_succ hi
  simp [blockEquiv, Equiv.symm, h]

private lemma blockEquiv_symm_ge
  (d : ℕ)
  (hd : 0 < d)
  (i : Fin (d + d))
  (hi : 2 ≤ (i : ℕ)) :
    (blockEquiv d hd).symm i =
      Sum.inr ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩ := by
  have h : ¬(i : ℕ) ≤ 1 := by omega
  simp [blockEquiv, Equiv.symm, h]

private lemma reindex_fromBlocks_apply
  (d : ℕ)
  (hd : 1 < d)
  (i j : Fin (d + d)) :
    (Matrix.reindex (blockEquiv d (by omega)) (blockEquiv d (by omega))
        (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
          (interleave (d - 1)))) i j =
      if hi : (i : ℕ) < 2 then
        if _ : (j : ℕ) < 2 then
          if (i : ℕ) = (j : ℕ) then (1 : ℝ) else 0
        else
          0
      else
        if _ : (j : ℕ) < 2 then
          0
        else
          interleave (d - 1)
            ⟨(i : ℕ) - 2, by have := i.isLt; omega⟩
            ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩ := by
  simp only [Matrix.reindex, Matrix.submatrix]
  if hi : (i : ℕ) < 2 then
    have hbi := blockEquiv_symm_lt d (by omega) i hi
    if hj : (j : ℕ) < 2 then
      have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, Matrix.fromBlocks_apply₁₁, Matrix.one_apply, Fin.ext_iff, hi, hj]
    else
      have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, Matrix.fromBlocks_apply₁₂, hi, hj]
  else
    have hbi := blockEquiv_symm_ge d (by omega) i (Nat.le_of_not_lt hi)
    if hj : (j : ℕ) < 2 then
      have hbj := blockEquiv_symm_lt d (by omega) j hj
      simp [hbi, hbj, Matrix.fromBlocks_apply₂₁, hi, hj]
    else
      have hbj := blockEquiv_symm_ge d (by omega) j (Nat.le_of_not_lt hj)
      simp [hbi, hbj, Matrix.fromBlocks_apply₂₂, hi, hj]

private lemma shift_mul_block
  (d : ℕ)
  (hd : 1 < d) :
    (shiftMatrix (α := ℝ) (⟨d, by have := hd; omega⟩ : Fin (d + d)) (⟨1, by have := hd; omega⟩ : Fin (d + d))) * interleave d =
      Matrix.reindex (blockEquiv d (by omega)) (blockEquiv d (by omega))
        (Matrix.fromBlocks (1 : Matrix (Fin 2) (Fin 2) ℝ) 0 0
          (interleave (d - 1))) := by
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

@[path]
private lemma main
  {d : ℕ}
-- given
  (hd : 1 < d) :
-- imply
  (interleave d).det = (-1 : ℝ) ^ (d - 1) * (interleave (d - 1)).det := by
-- proof
  let S := shiftMatrix (α := ℝ) (⟨d, by omega⟩ : Fin (d + d)) (⟨1, by omega⟩ : Fin (d + d))
  let P := interleave d
  have hS : S.det = (-1 : ℝ) ^ (d - 1) :=
    DetShiftMatrix.eq.PowNeg1Sub (α := ℝ) (i₀ := ⟨d, by omega⟩) (j₀ := ⟨1, by omega⟩) hd
  have hSP : (S * P).det = (interleave (d - 1)).det := by
    rw [shift_mul_block d hd, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_one, one_mul]
  have hprod : S.det * P.det = (interleave (d - 1)).det :=
    (Matrix.det_mul S P).symm.trans hSP
  -- multiply both sides by S.det = (-1)^(d-1)
  have hinv : S.det * S.det = 1 := by
    rw [hS]
    calc
      _ = ((-1 : ℝ) ^ 2) ^ (d - 1) := by rw [← pow_mul]; ring_nf
      _ = (1 : ℝ) ^ (d - 1) := by norm_num
      _ = 1 := by simp
  calc
    _ = 1 * P.det := by rw [one_mul]
    _ = (S.det * S.det) * P.det := by rw [hinv]
    _ = S.det * (S.det * P.det) := by ring
    _ = S.det * (interleave (d - 1)).det := by rw [hprod]
    _ = (-1 : ℝ) ^ (d - 1) * (interleave (d - 1)).det := by rw [hS]


-- created on 2026-11-01
