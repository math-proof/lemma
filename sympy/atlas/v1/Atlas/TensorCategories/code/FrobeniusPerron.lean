/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import sympy.atlas.v1.Atlas.TensorCategories.code.PerronFrobeniusProof
import Lemma.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof

set_option maxHeartbeats 400000

structure FusionRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  unit : ι
  N : ι → ι → ι → ℕ
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  unit_mul : ∀ j k, N unit j k = if j = k then 1 else 0
  mul_unit : ∀ i k, N i unit k = if i = k then 1 else 0
  duality : ∀ i j, N i j unit = if j = star i then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  N_star_transpose : ∀ i j k, N i j k = N (star i) k j

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

section Basic

variable (R : FusionRing ι)

def IsAntiAutomorphism (ψ : ι → ι) : Prop :=
  Function.Bijective ψ ∧
  ∀ i j k, R.N (ψ i) j k = R.N i k j

def IsTransitive : Prop :=
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N X Y Z) ∧
  (∀ X Z : ι, ∃ Y : ι, 0 < R.N Y X Z)

end Transitivity

section MulMatrix

variable (R : FusionRing ι)

def mulMatrix (i : ι) : Matrix ι ι ℕ :=
  Matrix.of (fun j k => R.N i j k)

def IsComplexEigenvalue (M : Matrix ι ι ℝ) (μ : ℂ) : Prop :=
  ∃ v : ι → ℂ, v ≠ 0 ∧
    (M.map (↑· : ℝ → ℂ)).mulVec v = μ • v

structure FPdimData where
  d : ι → ℝ
  d_unit : d R.unit = 1
  d_pos : ∀ i, d i > 0
  d_mul : ∀ i j, d i * d j = ∑ k : ι, (R.N i j k : ℝ) * d k

structure PerronFrobenius (M : Matrix ι ι ℝ) where
  ev : ℝ
  evec : ι → ℝ
  ev_pos : 0 < ev
  evec_pos : ∀ i, 0 < evec i
  is_eigenvec : M.mulVec evec = ev • evec
  unique : ∀ (μ : ℝ) (w : ι → ℝ), (∀ i, 0 < w i) →
    M.mulVec w = μ • w →
    ∃ c : ℝ, ∀ i, w i = c * evec i

class HasPerronFrobeniusProperty (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] where
  pfEigenvec : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v
  pfUnique : ∀ (M : Matrix ι ι ℝ), (∀ i j, 0 < M i j) →
    ∀ (r₁ r₂ : ℝ) (v w : ι → ℝ),
    (∀ i, 0 < v i) → M.mulVec v = r₁ • v →
    (∀ i, 0 < w i) → M.mulVec w = r₂ • w →
    ∃ c : ℝ, ∀ i, w i = c * v i

noncomputable def perron_frobenius_pos_matrix
    [Nonempty ι] [HasPerronFrobeniusProperty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := HasPerronFrobeniusProperty.pfEigenvec M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      HasPerronFrobeniusProperty.pfUnique M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

noncomputable def rightMulMatrix : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (∑ i : ι, R.N j i k : ℝ))

noncomputable def leftMulMatrixR (X : ι) : Matrix ι ι ℝ :=
  Matrix.of (fun j k => (R.N X j k : ℝ))

def leftMulMatrixZ (X : ι) : Matrix ι ι ℤ :=
  Matrix.of (fun j k => (R.N X j k : ℤ))

noncomputable def FPdim : ι → ℝ := fpd.d

noncomputable def catDim : ℝ :=
  ∑ i : ι, fpd.d i ^ 2

theorem proposition_1_45_5 :
    (fpd.d R.unit = 1 ∧
     (∀ i j, fpd.d i * fpd.d j = ∑ k : ι, (R.N i j k : ℝ) * fpd.d k)) ∧
    (∀ X, (R.leftMulMatrixR X).mulVec fpd.d = fpd.d X • fpd.d) ∧
    (∀ i, fpd.d i > 0) :=
  ⟨⟨fpd.d_unit, fpd.d_mul⟩, fpd.d_is_eigenvalue_of_mulMatrix, fpd.d_pos⟩

noncomputable instance : HasPerronFrobeniusProperty (Fin 1) where
  pfEigenvec := fun M hM => by
    refine ⟨M 0 0, fun _ => 1, hM 0 0, fun _ => one_pos, ?_⟩
    ext i
    have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
    subst hi
    simp [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  pfUnique := fun M _ r₁ r₂ v w hv _ hw _ => by
    exact ⟨w 0 / v 0, fun i => by
      have hi : i = (0 : Fin 1) := Subsingleton.elim i 0
      subst hi; rw [div_mul_cancel₀ _ (ne_of_gt (hv 0))]⟩

end PerronFrobeniusFin1

namespace PerronFrobeniusFin2

open FusionRing

noncomputable section

/-- Discriminant of the characteristic polynomial of a 2×2 matrix,
`(M₀₀ - M₁₁)² + 4 M₀₁ M₁₀`. -/
def pfDiscriminant (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 - M 1 1) ^ 2 + 4 * M 0 1 * M 1 0

/-- The larger root of the characteristic polynomial of a 2×2 matrix,
the candidate Perron–Frobenius eigenvalue. -/
def pfEigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) : ℝ :=
  (M 0 0 + M 1 1 + Real.sqrt (pfDiscriminant M)) / 2

/-- Explicit Perron–Frobenius eigenvector of a 2×2 matrix,
`(M 0 1, pfEigenvalue M - M 0 0)`. -/
def pfEigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → ℝ :=
  ![M 0 1, pfEigenvalue M - M 0 0]

/-- The discriminant `pfDiscriminant M` of a strictly positive 2×2
matrix is positive. -/
lemma pfDiscriminant_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfDiscriminant M := by
  unfold pfDiscriminant
  nlinarith [sq_nonneg (M 0 0 - M 1 1), hM 0 1, hM 1 0]

/-- The Perron–Frobenius eigenvalue of a strictly positive 2×2 matrix
is positive. -/
lemma pfEigenvalue_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    0 < pfEigenvalue M := by
  unfold pfEigenvalue
  linarith [pfDiscriminant_pos M hM |> Real.sqrt_pos_of_pos, hM 0 0, hM 1 1]

/-- For a strictly positive 2×2 matrix,
`M 0 0 - M 1 1 < sqrt(pfDiscriminant M)`. -/
lemma sqrt_disc_gt_diff (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M 0 0 - M 1 1 < Real.sqrt (pfDiscriminant M) := by
  have hΔ := pfDiscriminant_pos M hM
  have hΔ_ge : (M 0 0 - M 1 1) ^ 2 < pfDiscriminant M := by
    unfold pfDiscriminant; nlinarith [hM 0 1, hM 1 0]
  by_cases h : 0 ≤ M 0 0 - M 1 1
  · calc M 0 0 - M 1 1 = Real.sqrt ((M 0 0 - M 1 1) ^ 2) := (Real.sqrt_sq h).symm
      _ < Real.sqrt (pfDiscriminant M) := Real.sqrt_lt_sqrt (sq_nonneg _) hΔ_ge
  · linarith [Real.sqrt_pos_of_pos hΔ]

/-- The explicit eigenvector `pfEigenvec M` has strictly positive
entries when `M` does. -/
lemma pfEigenvec_pos (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    ∀ i, 0 < pfEigenvec M i := by
  intro i; fin_cases i
  · show 0 < (pfEigenvec M) 0
    simp [pfEigenvec, Matrix.cons_val_zero]; exact hM 0 1
  · show 0 < (pfEigenvec M) 1
    simp [pfEigenvec, Matrix.cons_val_one]
    unfold pfEigenvalue; linarith [sqrt_disc_gt_diff M hM]

/-- `pfEigenvalue M` is a root of the characteristic polynomial of `M`. -/
lemma pfEigenvalue_char_poly (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    pfEigenvalue M ^ 2 - (M 0 0 + M 1 1) * pfEigenvalue M +
    (M 0 0 * M 1 1 - M 0 1 * M 1 0) = 0 := by
  unfold pfEigenvalue pfDiscriminant
  have hΔ : 0 ≤ pfDiscriminant M := le_of_lt (pfDiscriminant_pos M hM)
  unfold pfDiscriminant at hΔ
  nlinarith [Real.sq_sqrt hΔ]

/-- `pfEigenvec M` is an eigenvector of `M` with eigenvalue
`pfEigenvalue M`. -/
lemma pfEigenvec_is_eigenvec (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j) :
    M.mulVec (pfEigenvec M) = pfEigenvalue M • pfEigenvec M := by
  ext i; fin_cases i
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]; ring
  ·
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, pfEigenvec,
          Matrix.cons_val_zero, Matrix.cons_val_one, Pi.smul_apply, smul_eq_mul]
    nlinarith [pfEigenvalue_char_poly M hM]

/-- Uniqueness of positive eigenvectors of a strictly positive 2×2
matrix up to scaling. -/
lemma pfUnique_fin2 (M : Matrix (Fin 2) (Fin 2) ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : Fin 2 → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i := by
  have hv0 := hv 0; have hv1 := hv 1; have hw0 := hw 0; have hw1 := hw 1
  have hv0_ne : v 0 ≠ 0 := ne_of_gt hv0
  have hv1_ne : v 1 ≠ 0 := ne_of_gt hv1
  have hw0_ne : w 0 ≠ 0 := ne_of_gt hw0
  have hw1_ne : w 1 ≠ 0 := ne_of_gt hw1

  have hrv0 : M 0 0 * v 0 + M 0 1 * v 1 = r₁ * v 0 := by
    have := congr_fun hev 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrv1 : M 1 0 * v 0 + M 1 1 * v 1 = r₁ * v 1 := by
    have := congr_fun hev 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw0 : M 0 0 * w 0 + M 0 1 * w 1 = r₂ * w 0 := by
    have := congr_fun hew 0
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith
  have hrw1 : M 1 0 * w 0 + M 1 1 * w 1 = r₂ * w 1 := by
    have := congr_fun hew 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
    linarith

  have hv_01 : (r₁ - M 0 0) * v 0 = M 0 1 * v 1 := by linarith
  have hv_10 : (r₁ - M 1 1) * v 1 = M 1 0 * v 0 := by linarith
  have hw_01 : (r₂ - M 0 0) * w 0 = M 0 1 * w 1 := by linarith

  have hr1_gt0 : M 0 0 < r₁ := by nlinarith [hM 0 1]
  have hr1_gt1 : M 1 1 < r₁ := by nlinarith [hM 1 0]
  have hr2_gt0 : M 0 0 < r₂ := by nlinarith [hM 0 1]
  have hr2_gt1 : M 1 1 < r₂ := by nlinarith [hM 1 0]

  have hcp1 : (r₁ - M 0 0) * (r₁ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₁ - M 0 0 = M 0 1 * v 1 / v 0 := by field_simp; linarith
    have hd : r₁ - M 1 1 = M 1 0 * v 0 / v 1 := by field_simp; linarith
    rw [ha, hd]; field_simp
  have hcp2 : (r₂ - M 0 0) * (r₂ - M 1 1) = M 0 1 * M 1 0 := by
    have ha : r₂ - M 0 0 = M 0 1 * w 1 / w 0 := by field_simp; linarith
    have hd : r₂ - M 1 1 = M 1 0 * w 0 / w 1 := by field_simp; linarith
    rw [ha, hd]; field_simp

  have hfact : (r₁ - r₂) * (r₁ + r₂ - (M 0 0 + M 1 1)) = 0 := by nlinarith

  have hr_eq : r₁ = r₂ := by
    rcases mul_eq_zero.mp hfact with h | h
    · linarith
    · exfalso; linarith

  rw [hr_eq] at hv_01

  have h_rne : r₂ - M 0 0 ≠ 0 := by linarith
  have hcross_eq : (r₂ - M 0 0) * (v 0 * w 1 - w 0 * v 1) = 0 := by
    have l1 : (r₂ - M 0 0) * v 0 * w 1 = M 0 1 * v 1 * w 1 := by
      have := congr_arg (· * w 1) hv_01; simp [mul_assoc] at this; linarith
    have l2 : (r₂ - M 0 0) * w 0 * v 1 = M 0 1 * w 1 * v 1 := by
      have := congr_arg (· * v 1) hw_01; simp [mul_assoc] at this; linarith
    linarith [mul_comm (v 1) (w 1)]

  have hcross : v 0 * w 1 = w 0 * v 1 := by
    rcases mul_eq_zero.mp hcross_eq with h | h
    · exact absurd h h_rne
    · linarith

  refine ⟨w 0 / v 0, ?_⟩
  intro i; fin_cases i
  · show w 0 = w 0 / v 0 * v 0
    rw [div_mul_cancel₀ _ hv0_ne]
  · show w 1 = w 0 / v 0 * v 1
    rw [div_mul_eq_mul_div, ← hcross, mul_div_cancel_left₀ _ hv0_ne]

end

noncomputable instance : HasPerronFrobeniusProperty (Fin 2) where
  pfEigenvec := fun M hM =>
    ⟨pfEigenvalue M, pfEigenvec M,
     pfEigenvalue_pos M hM, pfEigenvec_pos M hM, pfEigenvec_is_eigenvec M hM⟩
  pfUnique := fun M hM r₁ r₂ v w hv hev hw hew =>
    pfUnique_fin2 M hM r₁ r₂ v w hv hev hw hew

end PerronFrobeniusFin2

/-- Existence of a Perron–Frobenius eigenpair for any strictly positive
matrix: a positive eigenvalue `r` together with a strictly positive
eigenvector. -/
noncomputable def perronFrobeniusExistence {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  PerronFrobenius.perronFrobeniusExistence M hM

/-- General `HasPerronFrobeniusProperty` instance combining the existence
result `perronFrobeniusExistence` with the uniqueness
`PerronFrobeniusGeneral.pfUnique_general`. -/
noncomputable instance instHasPerronFrobeniusPropertyGeneral
    (ι : Type*) [DecidableEq ι] [Fintype ι] [Nonempty ι] :
    FusionRing.HasPerronFrobeniusProperty ι where
  pfEigenvec := fun M hM => perronFrobeniusExistence M hM
  pfUnique := fun M hM r₁ r₂ v w hv hev hw hew =>
    PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

section VerifyInstance

variable {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]

noncomputable example : FusionRing.HasPerronFrobeniusProperty ι := inferInstance

noncomputable example (R : FusionRing ι) : Nonempty R.FPdimData := R.exists_FPdimData

end VerifyInstance

/-- Existence part of EGNO Theorem 1.44.1: every strictly positive
matrix has a positive eigenvalue with a positive eigenvector. -/
noncomputable def theorem_1_44_1_existence
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    Σ' (r : ℝ) (v : ι → ℝ), 0 < r ∧ (∀ i, 0 < v i) ∧ M.mulVec v = r • v :=
  perronFrobeniusExistence M hM

/-- Uniqueness part of EGNO Theorem 1.44.1: any two positive
eigenvectors of a strictly positive matrix are scalar multiples
of each other. -/
theorem theorem_1_44_1_uniqueness
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j)
    (r₁ r₂ : ℝ) (v w : ι → ℝ)
    (hv : ∀ i, 0 < v i) (hev : M.mulVec v = r₁ • v)
    (hw : ∀ i, 0 < w i) (hew : M.mulVec w = r₂ • w) :
    ∃ c : ℝ, ∀ i, w i = c * v i :=
  PerronFrobeniusGeneral.pfUnique_general M hM r₁ r₂ v w hv hev hw hew

/-- EGNO Theorem 1.44.1 (Perron–Frobenius for strictly positive
matrices): existence and uniqueness of a Perron–Frobenius eigenpair,
bundled as a `PerronFrobenius M`. -/
noncomputable def theorem_1_44_1
    {ι : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 < M i j) :
    FusionRing.PerronFrobenius M :=
  let ⟨r, v, hr_pos, hv_pos, hv_eig⟩ := theorem_1_44_1_existence M hM
  { ev := r
    evec := v
    ev_pos := hr_pos
    evec_pos := hv_pos
    is_eigenvec := hv_eig
    unique := fun μ w hw_pos hw_eig =>
      theorem_1_44_1_uniqueness M hM r μ v w hv_pos hv_eig hw_pos hw_eig }

open FusionRing in

open FusionRing in

open FusionRing in

open FusionRing in

open FusionRing

namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable (R : FusionRing ι)

/-- Application of the Kronecker spectral extraction to the
Frobenius–Perron dimension: if `fpd.d i < 2` then `fpd.d i = 2 cos(π/n)`
for some integer `n ≥ 2`. -/
namespace FPdimData

variable {R}
variable (fpd : R.FPdimData)

/-- EGNO Corollary 1.45.16: if `fpd.d i < 2`, then
`fpd.d i = 2 cos(π/n)` for some integer `n ≥ 3`. -/
end FPdimData

end FusionRing
