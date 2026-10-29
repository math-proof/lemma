import Mathlib.LinearAlgebra.Matrix.Block
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.Echelon.Plu
open Matrix
set_option maxHeartbeats 800000


/-- Permutation factor of recursive PLU (`P` in `P * A = L * U`). -/
private noncomputable def pluP {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (plu n A).1

/-- Unit lower-triangular factor of recursive PLU. -/
private noncomputable def pluL {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (plu n A).2.1

/-- Upper-triangular factor of recursive PLU. -/
private noncomputable def pluU {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  (plu n A).2.2

private lemma swapMatrix_mul_apply
  {n : ℕ} (i j : Fin n) (A : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
  (swapMatrix i j * A) a b = A (Equiv.swap i j a) b := by
  classical
  simp [swapMatrix, Matrix.mul_apply, Matrix.of_apply]

private lemma swapMatrix_mul_self
  {n : ℕ} (i j : Fin n) :
  swapMatrix i j * swapMatrix i j = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  classical
  simp only [swapMatrix, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
  have hsum :
    (∑ k : Fin n, (if k = Equiv.swap i j a then (1 : ℂ) else 0) *
        (if b = Equiv.swap i j k then 1 else 0)) =
      if a = b then (1 : ℂ) else 0 := calc
      _ = ∑ k : Fin n, if k = Equiv.swap i j a then
          (if b = Equiv.swap i j k then (1 : ℂ) else 0) else 0 := by
        congr; ext k; split_ifs <;> ring
      _ = if b = Equiv.swap i j (Equiv.swap i j a) then (1 : ℂ) else 0 := by
        simp [Finset.sum_ite_eq']
      _ = if a = b then 1 else 0 := by
        simp [Equiv.swap_apply_self, eq_comm]
  simpa using hsum

private lemma pluBorderDiag_mul_pluBorderLower
  {n : ℕ} (P L : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ) :
  pluBorderDiag P * pluBorderLower d L =
      pluBorderLower (P.mulVec d) (P * L) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag, pluBorderLower]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag, pluBorderLower]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag, pluBorderLower,
        Matrix.mulVec, dotProduct]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag, pluBorderLower]

private lemma pluBorderLower_mul_pluBorderLower_one
  {n : ℕ} (d e : Fin n → ℂ) :
  pluBorderLower d (1 : Matrix (Fin n) (Fin n) ℂ) *
      pluBorderLower e (1 : Matrix (Fin n) (Fin n) ℂ) =
    pluBorderLower (d + e) (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, Matrix.one_apply]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, Matrix.one_apply,
        Pi.add_apply]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, Matrix.one_apply]

private lemma pluBorderLower_zero_one
  {n : ℕ} :
  pluBorderLower (fun _ : Fin n => (0 : ℂ)) (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderLower, Matrix.one_apply]
    | succ j =>
      simp [pluBorderLower, Matrix.one_apply]
      exact (Fin.succ_ne_zero j).symm
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderLower, Matrix.one_apply]
    | succ j =>
      simp [pluBorderLower, Matrix.one_apply]

private lemma pluBorderLower_mul_self_inv
  {n : ℕ} (ℓ : Fin n → ℂ) :
  pluBorderLower (-ℓ) (1 : Matrix (Fin n) (Fin n) ℂ) *
      pluBorderLower ℓ (1 : Matrix (Fin n) (Fin n) ℂ) =
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [pluBorderLower_mul_pluBorderLower_one, ← pluBorderLower_zero_one]
  congr 1
  ext i
  simp

private lemma pluBorderLower_mul_self_inv_left
  {n : ℕ} (ℓ : Fin n → ℂ) :
  pluBorderLower ℓ (1 : Matrix (Fin n) (Fin n) ℂ) *
      pluBorderLower (-ℓ) (1 : Matrix (Fin n) (Fin n) ℂ) =
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [pluBorderLower_mul_pluBorderLower_one, ← pluBorderLower_zero_one]
  congr 1
  ext i
  simp

private lemma pluBorderLower_mul_pluBorderUpper_apply
  {n : ℕ} (d : Fin n → ℂ) (L : Matrix (Fin n) (Fin n) ℂ)
  (c : ℂ) (u : Fin n → ℂ) (U : Matrix (Fin n) (Fin n) ℂ) :
  (pluBorderLower d L * pluBorderUpper c u U) 0 0 = c ∧
    (∀ j : Fin n, (pluBorderLower d L * pluBorderUpper c u U) 0 j.succ = u j) ∧
    (∀ i : Fin n, (pluBorderLower d L * pluBorderUpper c u U) i.succ 0 = c * d i) ∧
    (∀ i j : Fin n, (pluBorderLower d L * pluBorderUpper c u U) i.succ j.succ =
      d i * u j + (L * U) i j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, pluBorderUpper]
  ·
    intro j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, pluBorderUpper]
  ·
    intro i
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, pluBorderUpper]
    ring
  ·
    intro i j
    simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderLower, pluBorderUpper]

private lemma pluBorderLower_mul_pluBorderUpper_congr
  {n : ℕ} (d : Fin n → ℂ) (L L' U U' : Matrix (Fin n) (Fin n) ℂ)
  (c : ℂ) (u : Fin n → ℂ)
  (h : L * U = L' * U') :
  pluBorderLower d L * pluBorderUpper c u U =
      pluBorderLower d L' * pluBorderUpper c u U' := by
  ext i j
  have hL := pluBorderLower_mul_pluBorderUpper_apply d L c u U
  have hR := pluBorderLower_mul_pluBorderUpper_apply d L' c u U'
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      rw [hL.1, hR.1]
    | succ j =>
      rw [hL.2.1 j, hR.2.1 j]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      rw [hL.2.2.1 i, hR.2.2.1 i]
    | succ j =>
      rw [hL.2.2.2 i j, hR.2.2.2 i j, h]

private lemma elimBlock_eq_pluBorderLower
  {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
  elimBlock B 0 =
      pluBorderLower (fun i : Fin n => elimBlock B 0 i.succ 0)
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext a b
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero =>
      simp [elimBlock, pluBorderLower]
    | succ b =>
      simp [elimBlock, pluBorderLower, Matrix.one_apply]
      exact (Fin.succ_ne_zero b).symm
  | succ a =>
    cases b using Fin.cases with
    | zero =>
      simp [elimBlock, pluBorderLower]
    | succ b =>
      simp [elimBlock, pluBorderLower, Matrix.one_apply]

private lemma pivot_swap_col_zero
  {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  (hB00 : (swapMatrix (0 : Fin (n + 1)) (pivotRow A 0) * A) 0 0 = 0)
  (i : Fin (n + 1)) :
  (swapMatrix (0 : Fin (n + 1)) (pivotRow A 0) * A) i 0 = 0 := by
  set S := swapMatrix (0 : Fin (n + 1)) (pivotRow A 0)
  set B := S * A
  change B 0 0 = 0 at hB00
  have hBA : ∀ a b, B a b = A (Equiv.swap 0 (pivotRow A 0) a) b := by
    intro a b
    simpa [S, B] using swapMatrix_mul_apply (0 : Fin (n + 1)) (pivotRow A 0) A a b
  have hA0 : ∀ r : Fin (n + 1), A r 0 = 0 := by
    intro r
    by_contra hr
    have hne : (Finset.univ.filter fun x : Fin (n + 1) =>
        (0 : Fin (n + 1)) ≤ x ∧ A x 0 ≠ 0).Nonempty :=
      ⟨r, by simp [hr]⟩
    have hpr : pivotRow A 0 =
        (Finset.univ.filter fun x : Fin (n + 1) =>
          (0 : Fin (n + 1)) ≤ x ∧ A x 0 ≠ 0).min' hne := by
      dsimp only [pivotRow]
      rw [dite_eq_left hne]
    have hp : A (pivotRow A 0) 0 ≠ 0 := by
      have hin :=
        Finset.min'_mem
          (Finset.univ.filter fun x : Fin (n + 1) =>
            (0 : Fin (n + 1)) ≤ x ∧ A x 0 ≠ 0) hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hin
      simpa [hpr] using hin.2
    have : B 0 0 ≠ 0 := by
      rwa [hBA, Equiv.swap_apply_left]
    exact this hB00
  change B i 0 = 0
  rw [hBA, hA0]

private lemma elimBlock_mul_first_col_zero
  {n : ℕ} (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  (hcol : B 0 0 = 0 → ∀ i : Fin (n + 1), B i 0 = 0) :
  ∀ i : Fin n, (elimBlock B 0 * B) i.succ 0 = 0 := by
  intro i
  set E := elimBlock B 0
  have hz :
    (E * B) i.succ 0 =
      E i.succ 0 * B 0 0 + ∑ j : Fin n, E i.succ j.succ * B j.succ 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_succ]
  have hdiag : ∀ j : Fin n, E i.succ j.succ = (if i = j then (1 : ℂ) else 0) := by
    intro j
    simp [E, elimBlock, Fin.succ_ne_zero]
  have hsum :
    (∑ j : Fin n, E i.succ j.succ * B j.succ 0) = B i.succ 0 := by
    simp [hdiag, Finset.sum_ite_eq]
  rw [hz, hsum]
  if hp : B 0 0 = 0 then
    have hi := hcol hp i.succ
    have hE0 : E i.succ 0 = 0 := by
      simp [E, elimBlock, hp]
    simp [hE0, hi]
  else
    have hE0 : E i.succ 0 = -B i.succ 0 / B 0 0 := by
      simp [E, elimBlock, hp]
    rw [hE0]
    field_simp [hp]
    ring

private lemma eq_pluBorderUpper_of_col_zero
  {n : ℕ} (C : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  (hz : ∀ i : Fin n, C i.succ 0 = 0) :
  C = pluBorderUpper (C 0 0) (fun j => C 0 j.succ) (trailingSubmatrix C) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderUpper]
    | succ j =>
      simp [pluBorderUpper]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderUpper, hz]
    | succ j =>
      simp [pluBorderUpper, trailingSubmatrix]

private lemma swapMatrix_transpose_eq
  {n : ℕ} (i j : Fin n) :
  (swapMatrix i j)ᵀ = swapMatrix i j := by
  ext a b
  simp only [swapMatrix, Matrix.transpose_apply, Matrix.of_apply]
  split_ifs with h1 h2 h2
  · rfl
  ·
    have : b = Equiv.swap i j a := by
      rw [h1, Equiv.swap_apply_self]
    contradiction
  ·
    have : a = Equiv.swap i j b := by
      rw [h2, Equiv.swap_apply_self]
    contradiction
  · rfl

private lemma swapMatrix_mul_transpose
  {n : ℕ} (i j : Fin n) :
  swapMatrix i j * (swapMatrix i j)ᵀ = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  rw [swapMatrix_transpose_eq, swapMatrix_mul_self]

private lemma pluBorderDiag_mul
  {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
  pluBorderDiag A * pluBorderDiag B = pluBorderDiag (A * B) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag]
    | succ j =>
      simp [Matrix.mul_apply, Fin.sum_univ_succ, pluBorderDiag]

private lemma pluBorderDiag_transpose
  {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
  (pluBorderDiag M)ᵀ = pluBorderDiag Mᵀ := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderDiag, Matrix.transpose_apply]
    | succ j =>
      simp [pluBorderDiag, Matrix.transpose_apply]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderDiag, Matrix.transpose_apply]
    | succ j =>
      simp [pluBorderDiag, Matrix.transpose_apply]

private lemma pluBorderDiag_one
  {n : ℕ} :
  pluBorderDiag (1 : Matrix (Fin n) (Fin n) ℂ) =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderDiag, Matrix.one_apply]
    | succ j =>
      simp [pluBorderDiag, Matrix.one_apply]
      exact (Fin.succ_ne_zero j).symm
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderDiag, Matrix.one_apply]
    | succ j =>
      simp [pluBorderDiag, Matrix.one_apply]

private lemma pluBorderDiag_mul_transpose
  {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
  (h : M * Mᵀ = 1) :
  pluBorderDiag M * (pluBorderDiag M)ᵀ =
      (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) := by
  rw [pluBorderDiag_transpose, pluBorderDiag_mul, h, pluBorderDiag_one]

private lemma mul_transpose_of_mul
  {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℂ}
  (hA : A * Aᵀ = 1) (hB : B * Bᵀ = 1) :
  (A * B) * (A * B)ᵀ = 1 :=
  calc
    _ = A * B * (Bᵀ * Aᵀ) := by
      rw [Matrix.transpose_mul]
    _ = A * (B * Bᵀ) * Aᵀ := by
      simp [Matrix.mul_assoc]
    _ = A * 1 * Aᵀ := by
      rw [hB]
    _ = A * Aᵀ := by
      simp
    _ = 1 := hA

private lemma pluBorderLower_isLowerTriangular
  {n : ℕ} (d : Fin n → ℂ) {L₀ : Matrix (Fin n) (Fin n) ℂ}
  (hL : L₀.IsLowerTriangular) :
  (pluBorderLower d L₀).IsLowerTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    cases j using Fin.cases with
    | zero =>
      exact (lt_irrefl _ hij).elim
    | succ j =>
      simp [pluBorderLower]
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      exact (Fin.not_lt_zero _ hij).elim
    | succ j =>
      have hij' : i < j := Fin.succ_lt_succ_iff.mp hij
      simp [pluBorderLower]
      exact hL hij'

private lemma pluBorderUpper_isUpperTriangular
  {n : ℕ} (c : ℂ) (u : Fin n → ℂ) {U₀ : Matrix (Fin n) (Fin n) ℂ}
  (hU : U₀.IsUpperTriangular) :
  (pluBorderUpper c u U₀).IsUpperTriangular := by
  intro i j hij
  cases i using Fin.cases with
  | zero =>
    exact (Fin.not_lt_zero _ hij).elim
  | succ i =>
    cases j using Fin.cases with
    | zero =>
      simp [pluBorderUpper]
    | succ j =>
      have hij' : j < i := Fin.succ_lt_succ_iff.mp hij
      simp [pluBorderUpper]
      exact hU hij'

private lemma one_isLowerTriangular
  {n : ℕ} :
  (1 : Matrix (Fin n) (Fin n) ℂ).IsLowerTriangular := by
  intro i j hij
  simp [Matrix.one_apply]
  exact ne_of_lt hij

private lemma one_isUpperTriangular
  {n : ℕ} :
  (1 : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular := by
  intro i j hij
  simp [Matrix.one_apply]
  exact ne_of_gt hij

private lemma plu_factors_props
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  pluP A * (pluP A)ᵀ = 1 ∧
    (pluL A).IsLowerTriangular ∧
    (pluU A).IsUpperTriangular := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · simp [pluP, plu]
    · simpa [pluL, plu] using one_isLowerTriangular (n := 0)
    · simpa [pluU, plu] using one_isUpperTriangular (n := 0)
  | succ n ih =>
    set S := swapMatrix (0 : Fin (n + 1)) (pivotRow A 0)
    set B := S * A
    set E := elimBlock B 0
    set C := E * B
    set T := trailingSubmatrix C
    set P' := pluP T
    set L' := pluL T
    set U' := pluU T
    set ℓ : Fin n → ℂ := fun i => -E i.succ 0
    have hP : pluP A = pluBorderDiag P' * S := by
      dsimp [pluP, plu, S, B, E, C, T, P']
    have hL : pluL A = pluBorderLower (P'.mulVec ℓ) L' := by
      simp only [pluL, pluP, plu, P', L', T, C, E, B, S, ℓ]
    have hU : pluU A = pluBorderUpper (C 0 0) (fun j => C 0 j.succ) U' := by
      simp only [pluU, plu, U', T, C, E, B, S]
    have hP' : P' * P'ᵀ = 1 := (ih T).1
    have hL' : L'.IsLowerTriangular := (ih T).2.1
    have hU' : U'.IsUpperTriangular := (ih T).2.2
    refine ⟨?_, ?_, ?_⟩
    ·
      simpa [hP] using mul_transpose_of_mul
        (pluBorderDiag_mul_transpose P' hP')
        (swapMatrix_mul_transpose _ _)
    ·
      rw [hL]
      exact pluBorderLower_isLowerTriangular _ hL'
    ·
      rw [hU]
      exact pluBorderUpper_isUpperTriangular _ _ hU'

private lemma pluP_mul_transpose_eq_one
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  pluP A * (pluP A)ᵀ = 1 :=
  (plu_factors_props A).1

private lemma pluL_isLowerTriangular
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  (pluL A).IsLowerTriangular :=
  (plu_factors_props A).2.1

private lemma pluU_isUpperTriangular
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  (pluU A).IsUpperTriangular :=
  (plu_factors_props A).2.2

private lemma plu_mul_eq
  {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
  pluP A * A = pluL A * pluU A := by
  induction n with
  | zero =>
    have hA : A = 1 := Subsingleton.elim _ _
    simp [pluP, pluL, pluU, plu, hA]
  | succ n ih =>
    set S := swapMatrix (0 : Fin (n + 1)) (pivotRow A 0)
    set B := S * A
    set E := elimBlock B 0
    set C := E * B
    set T := trailingSubmatrix C
    set P' := pluP T
    set L' := pluL T
    set U' := pluU T
    set ℓ : Fin n → ℂ := fun i => -E i.succ 0
    have hP : pluP A = pluBorderDiag P' * S := by
      dsimp [pluP, plu, S, B, E, C, T, P']
    have hL : pluL A = pluBorderLower (P'.mulVec ℓ) L' := by
      simp only [pluL, pluP, plu, P', L', T, C, E, B, S, ℓ]
    have hU : pluU A = pluBorderUpper (C 0 0) (fun j => C 0 j.succ) U' := by
      simp only [pluU, plu, U', T, C, E, B, S]
    have hE : E = pluBorderLower (-ℓ) (1 : Matrix (Fin n) (Fin n) ℂ) := by
      dsimp [E]
      rw [elimBlock_eq_pluBorderLower]
      congr 1
      ext i
      dsimp [ℓ, E]
      ring
    have hcol : B 0 0 = 0 → ∀ i : Fin (n + 1), B i 0 = 0 := by
      intro h00 i
      simpa [S, B] using pivot_swap_col_zero A h00 i
    have hz : ∀ i : Fin n, C i.succ 0 = 0 := by
      simpa [C, E] using elimBlock_mul_first_col_zero B hcol
    have hC : C = pluBorderUpper (C 0 0) (fun j => C 0 j.succ) T := by
      simpa [T] using eq_pluBorderUpper_of_col_zero C hz
    have hEinvL : pluBorderLower ℓ (1 : Matrix (Fin n) (Fin n) ℂ) * E = 1 := by
      rw [hE]
      simpa using pluBorderLower_mul_self_inv_left ℓ
    have hB : B = pluBorderLower ℓ (1 : Matrix (Fin n) (Fin n) ℂ) * C := calc
      _ = 1 * B := by simp
      _ = (pluBorderLower ℓ 1 * E) * B := by rw [hEinvL]
      _ = pluBorderLower ℓ 1 * (E * B) := by rw [Matrix.mul_assoc]
      _ = pluBorderLower ℓ 1 * C := rfl
    have hPA : pluP A * A = pluBorderDiag P' * B := by
      rw [hP, Matrix.mul_assoc]
    have hPA' : pluP A * A =
        pluBorderLower (P'.mulVec ℓ) P' *
          pluBorderUpper (C 0 0) (fun j => C 0 j.succ) T := by
      rw [hPA, hB, ← Matrix.mul_assoc, pluBorderDiag_mul_pluBorderLower,
        Matrix.mul_one]
      exact congrArg (fun M => pluBorderLower (P'.mulVec ℓ) P' * M) hC
    have hIH : P' * T = L' * U' := ih T
    rw [hPA', hL, hU]
    exact pluBorderLower_mul_pluBorderUpper_congr (P'.mulVec ℓ) P' L' T U'
      (C 0 0) (fun j => C 0 j.succ) hIH

/--
[PLU decomposition](https://en.wikipedia.org/wiki/LU_decomposition#PLU_decomposition)
-/
@[path]
private lemma main
  {n : ℕ}
  {X : Matrix (Fin n) (Fin n) ℂ} :
-- imply
  let P := pluP X
  let L := pluL X
  let U := pluU X
  P * Pᵀ = 1 ∧
    L.IsLowerTriangular ∧
    U.IsUpperTriangular ∧
    P * X = L * U :=
-- proof
  ⟨pluP_mul_transpose_eq_one X, pluL_isLowerTriangular X, pluU_isUpperTriangular X, plu_mul_eq X⟩


-- created on 2026-10-07
-- updated on 2026-10-28
