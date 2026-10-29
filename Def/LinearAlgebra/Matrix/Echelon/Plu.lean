import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Order.Interval.Finset.Fin
open Matrix


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

/-- Trailing `n × n` block after dropping row / column `0`. -/
def trailingSubmatrix {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun i j => M i.succ j.succ

/-- Block diagonal `diag(1, M)` on `Fin (n + 1)` (GaussPivot `Fin.cases` bordering). -/
def pluBorderDiag {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.cases (Fin.cases (1 : ℂ) fun _ => 0) fun i => Fin.cases 0 fun j => M i j

/-- Unit lower border `[[1, 0], [d, L₀]]` (same shape as `gaussPivotBorderLower`). -/
def pluBorderLower {n : ℕ} (d : Fin n → ℂ) (L₀ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.cases (Fin.cases (1 : ℂ) fun _ => 0) fun i => Fin.cases (d i) fun j => L₀ i j

/-- Upper border `[[c, u], [0, U₀]]`. -/
def pluBorderUpper {n : ℕ} (c : ℂ) (u : Fin n → ℂ) (U₀ : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  Fin.cases (Fin.cases c fun j => u j) fun i => Fin.cases 0 fun j => U₀ i j

/-- One PLU elimination step: swap `S`, elim `E`, and `C = E * S * A`
(zeros below the `(0, 0)` entry; trailing block is the Schur complement). -/
noncomputable def pluStep {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ×
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ ×
      Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  let S := swapMatrix 0 (pivotRow A 0)
  let B := S * A
  let E := elimBlock B 0
  (S, E, E * B)

/-- Recursive PLU factors `(P, L, U)` assembled so that `P * A = L * U` when pivots work
(hence `A = P⁻¹ * L * U`; correctness lives in `Lemma/Matrix/`).

* `n = 0`: `P = L = U = 1`
* `n = n' + 1`: let `(S, E, C) = pluStep A`, `(P', L', U') = plu` on `trailingSubmatrix C`,
  and `ℓ i = -(E i.succ 0)`; then
  `P = pluBorderDiag P' * S`,
  `L = pluBorderLower (P'.mulVec ℓ) L'`,
  `U = pluBorderUpper (C 0 0) (fun j => C 0 j.succ) U'`. -/
noncomputable def plu :
    (n : ℕ) → Matrix (Fin n) (Fin n) ℂ →
      Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ
  | 0, _ => (1, 1, 1)
  | n + 1, A =>
    let S := swapMatrix 0 (pivotRow A 0)
    let B := S * A
    let E := elimBlock B 0
    let C := E * B
    let T := trailingSubmatrix C
    let (P', L', U') := plu n T
    let ℓ : Fin n → ℂ := fun i => -E i.succ 0
    (pluBorderDiag P' * S,
      pluBorderLower (mulVec P' ℓ) L',
      pluBorderUpper (C 0 0) (fun j => C 0 j.succ) U')
