import Initialize.Tactic.Attr.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Data.Matrix.Basic
import Def.LinearAlgebra.Matrix.Permutation
import Lemma.Fin.Sum_Delta.eq.One
import Lemma.Matrix.GetMatPowShiftMatrix.eq.DeltaModAdd
import Lemma.Nat.Delta.eq.Ite
open Matrix Finset Nat


/-- ∑_{k=1}^{n-1} δ((i+k)%n, j) = if i = j then 0 else 1 -/
private lemma sum_delta_ico
  (i j : Fin n) :
    ∑ k ∈ Finset.Ico 1 n, KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) =
      if i = j then 0 else 1 := by
  have h : 0 < n := Fin.pos i
  let z : Fin n := ⟨0, h⟩
  have hcomm : ∀ (x : Fin n), (((i : ℕ) + (x : ℕ)) % n) = ((x + i : Fin n) : ℕ) := by
    intro x
    rw [Fin.val_add, add_comm (x : ℕ) (i : ℕ)]
  have hinj : Set.InjOn (fun x : Fin n => (x : ℕ)) (Finset.univ.erase z) :=
    fun _ _ _ _ hcon => Fin.ext hcon
  have hval : Finset.image (fun x : Fin n => (x : ℕ)) Finset.univ = Finset.range n := by
    ext k
    simp [Fin.exists_iff]
  have himg :
    Finset.image (fun x : Fin n => (x : ℕ)) (Finset.univ.erase z) = Finset.Ico 1 n := by
    rw [Finset.image_erase (fun _ _ hcon => Fin.ext hcon), hval]
    ext k
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico, z]
    omega
  rw [← himg, Finset.sum_image hinj]
  simp_rw [hcomm]
  have hall :
    KroneckerDelta (i : ℕ) (j : ℕ) +
      ∑ x ∈ Finset.univ.erase z, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) = 1 := by
    have hfull := Fin.Sum_Delta.eq.One i j
    have hz :
      KroneckerDelta ((z + i : Fin n) : ℕ) (j : ℕ) = KroneckerDelta (i : ℕ) (j : ℕ) := by
      have hzval : (z : ℕ) = 0 := by simp [z]
      have hz0 : (z + i : Fin n).val = (i : ℕ) := by
        rw [Fin.val_add, hzval, Nat.zero_add, Nat.mod_eq_of_lt i.is_lt]
      rw [Fin.ext hz0]
    rw [← Finset.add_sum_erase Finset.univ
      (fun x => KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ)) (Finset.mem_univ z)] at hfull
    rwa [hz] at hfull
  have hkd : KroneckerDelta (i : ℕ) (j : ℕ) = if i = j then (1 : ℕ) else 0 := by
    simp [Delta.eq.Ite, Fin.ext_iff]
  apply Nat.add_left_cancel (n := KroneckerDelta (i : ℕ) (j : ℕ))
  rw [hall, hkd]
  split_ifs <;> rfl

/--
`det (J - 1) = (-1)^(n-1) * (n - 1)` where off-diagonal is 1 and diagonal is 0.
-/
private lemma det_offDiag_ones
  [CommRing α]
  (n : ℕ)
  (h : 0 < n) :
    Matrix.det (fun i j : Fin n => if i = j then (0 : α) else 1) =
      (-1 : α) ^ (n - 1) * (n - 1 : ℕ) := by
  let u : Fin n → α := fun _ => 1
  let J := Matrix.replicateCol (Fin 1) u * Matrix.replicateRow (Fin 1) u
  have hJ : ∀ (i j : Fin n), J i j = (1 : α) := by
    intro i j
    simp only [J, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.replicateRow_apply]
    rw [Finset.sum_eq_single (0 : Fin 1)]
    ·
      simp only [u]
      exact one_mul (1 : α)
    ·
      intro x _ hx
      exact False.elim (hx (Fin.fin_one_eq_zero x))
    ·
      intro hx
      exact False.elim (hx (Finset.mem_univ (0 : Fin 1)))
  have hM : (fun i j : Fin n => if i = j then (0 : α) else 1) =
      J - (1 : Matrix (Fin n) (Fin n) α) := by
    ext i j
    rw [Matrix.sub_apply, hJ i j, Matrix.one_apply]
    split_ifs <;> simp
  rw [hM]
  have hneg : J - (1 : Matrix (Fin n) (Fin n) α) =
      - ((1 : Matrix (Fin n) (Fin n) α) - J) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_apply, hJ i j]
    ring
  rw [hneg, Matrix.det_neg]
  rw [Matrix.det_one_sub_mul_comm
    (A := Matrix.replicateCol (Fin 1) u) (B := Matrix.replicateRow (Fin 1) u)]
  have h1 :
    Matrix.det
      ((1 : Matrix (Fin 1) (Fin 1) α) -
        Matrix.replicateRow (Fin 1) u * Matrix.replicateCol (Fin 1) u) =
      1 - (n : α) := by
    simp [Matrix.replicateRow_mul_replicateCol_apply, dotProduct, u, Finset.sum_const]
  rw [h1]
  have hn : n = (n - 1) + 1 := by omega
  rw [hn]
  simp [pow_succ]

@[path]
private lemma main
  [CommRing α]
  {n : ℕ}
-- given
  (hn : 0 < n)
  (A : Matrix (Fin n) (Fin n) α) :
-- imply
  (∑ k ∈ Finset.Ico 1 n,
      (shiftMatrix (α := α) ⟨0, hn⟩ ⟨n - 1, by omega⟩ ^ k) * A).det =
    ((-1 : α) ^ (n - 1) * (n - 1 : ℕ)) * A.det := by
-- proof
  let S := shiftMatrix (α := α) ⟨0, hn⟩ ⟨n - 1, by omega⟩
  let P : Matrix (Fin n) (Fin n) α := ∑ k ∈ Finset.Ico 1 n, S ^ k
  have hsum :
    (∑ k ∈ Finset.Ico 1 n, (S ^ k) * A) = P * A := by
    simp only [P, Finset.sum_mul]
  rw [hsum, Matrix.det_mul]
  have hP : P = fun i j : Fin n => if i = j then (0 : α) else 1 := by
    ext i j
    change (∑ k ∈ Finset.Ico 1 n, S ^ k) i j = _
    rw [Matrix.sum_apply]
    have hdelta (c : ℕ) (hc : c ∈ Finset.Ico 1 n) :
      (S ^ c) i j = (KroneckerDelta (((i : ℕ) + c) % n) (j : ℕ) : α) := by
      simpa [S] using GetMatPowShiftMatrix.eq.DeltaModAdd (α := α) c i j
    refine Eq.trans (Finset.sum_congr rfl fun c hc => hdelta c hc) ?_
    have :
      (∑ k ∈ Finset.Ico 1 n,
          (KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ) : α)) =
        (↑(∑ k ∈ Finset.Ico 1 n,
            KroneckerDelta (((i : ℕ) + k) % n) (j : ℕ)) : α) := by
      simp [Nat.cast_sum]
    rw [this, sum_delta_ico i j]
    split_ifs <;> simp
  rw [hP, det_offDiag_ones (α := α) n hn]


-- created on 2026-11-01
