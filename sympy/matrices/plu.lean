import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin

open Matrix

/-- Undo operator of a PLU (partial-pivoting Gaussian elimination) sweep.  Step `k` of the sweep
maps `A k` to `A (k + 1) = L k * (S k * A k)`, where `S k` is the row-swap (permutation) matrix of
the pivot and `L k` the elimination (unit lower-triangular) block; `pluUndo S L m` is
`(S 0)ᵀ (L 0)⁻¹ (S 1)ᵀ (L 1)⁻¹ ⋯ (S (m-1))ᵀ (L (m-1))⁻¹`. -/
noncomputable def pluUndo {n : ℕ} (S L : ℕ → Matrix (Fin n) (Fin n) ℂ) : ℕ → Matrix (Fin n) (Fin n) ℂ
  | 0 => 1
  | m + 1 => pluUndo S L m * ((S m)ᵀ * (L m)⁻¹)

/-- py `SwapMatrix(n, i, j)`: the permutation matrix of the transposition `(i j)`. -/
def swapMatrix {n : ℕ} (i j : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b => if b = Equiv.swap i j a then 1 else 0

/-- py `k + ReducedArgMax(Sign(Abs(M[k:, k])))`: the first row `r ≥ k` with `M r k ≠ 0`
(argmax of the 0/1 vector `sign |M[k:, k]|`, first index on ties), or `k` if there is none. -/
noncomputable def pivotRow {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) : Fin n :=
  if h : (Finset.univ.filter fun r => k ≤ r ∧ M r k ≠ 0).Nonempty then
    (Finset.univ.filter fun r => k ≤ r ∧ M r k ≠ 0).min' h
  else k

/-- py elimination block of step `k`: identity, except that column `k` below the diagonal is
`-B[k+1:, k] / B[k, k]` (or `0` when `B[k, k] = 0`). -/
noncomputable def elimBlock {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (k : Fin n) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun a b =>
    if a = b then 1
    else if b = k ∧ k < a then (if B k k = 0 then 0 else -B a k / B k k)
    else 0

/-- Telescoping form of a PLU sweep: `X = (S 0)ᵀ (L 0)⁻¹ ⋯ (S (m-1))ᵀ (L (m-1))⁻¹ A m`. -/
theorem pluUndo_spec {n : ℕ} {X : Matrix (Fin n) (Fin n) ℂ} {A B S L : ℕ → Matrix (Fin n) (Fin n) ℂ}
    (h₀ : X = A 0) (h₁ : ∀ k, B k = S k * A k) (h₂ : ∀ k, A (k + 1) = L k * B k)
    (h₃ : ∀ k, (S k)ᵀ * S k = 1) (h₄ : ∀ k, IsUnit (L k).det) :
    ∀ m, X = pluUndo S L m * A m := by
  intro m
  induction m with
  | zero =>
    rw [h₀, pluUndo, Matrix.one_mul]
  | succ m ih =>
    rw [ih, pluUndo, h₂ m, h₁ m]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (L m)⁻¹ (L m), Matrix.nonsing_inv_mul _ (h₄ m), Matrix.one_mul,
      ← Matrix.mul_assoc (S m)ᵀ, h₃ m, Matrix.one_mul]


-- created on 2026-09-27
