import sympy.matrices.plu
import sympy.Basic
open Matrix


/-- py's literal conclusion: `X = MatProd[k:n](SwapMatrix(n, k, pivot k)ᵀ) @ MatProd[k:n](block k) @ B[n-1]`. -/
@[main]
private lemma main
  {n : ℕ}
  {X : Matrix (Fin n) (Fin n) ℂ}
  {A B : ℕ → Matrix (Fin n) (Fin n) ℂ}
-- given
  (_h₀ : A 0 = X)
  (_h₁ : ∀ k : Fin n, B k = swapMatrix k (pivotRow (A k) k) * A k)
  (_h₂ : ∀ k : Fin n, A (k + 1) = elimBlock (B k) k * B k) :
-- imply
  X = (List.ofFn fun k : Fin n => (swapMatrix k (pivotRow (A k) k))ᵀ).prod *
    (List.ofFn fun k : Fin n => elimBlock (B k) k).prod * B (n - 1) := by
-- proof
  -- sorry: false as stated in py (see sorry_log.md, session 8): the elimination blocks enter
  -- un-inverted and the swaps are not interleaved with them.  Counterexample n = 2,
  -- X = !![1, 0; 1, 1]: no swaps, elimBlock (B 0) 0 = !![1, 0; -1, 1], B 1 = 1, so the rhs is
  -- !![1, 0; -1, 1] ≠ X.  The valid statement is the telescoping `pluUndo_spec` below.
  sorry


/-- Helper (valid form): the telescoping PLU identity `X = pluUndo S L m * A m`. -/
private lemma telescope
  {n : ℕ}
  {X : Matrix (Fin n) (Fin n) ℂ}
  {A B S L : ℕ → Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : X = A 0)
  (h₁ : ∀ k, B k = S k * A k)
  (h₂ : ∀ k, A (k + 1) = L k * B k)
  (h₃ : ∀ k, (S k)ᵀ * S k = 1)
  (h₄ : ∀ k, IsUnit (L k).det) :
-- imply
  ∀ m, X = pluUndo S L m * A m :=
  pluUndo_spec h₀ h₁ h₂ h₃ h₄


-- created on 2023-08-19
