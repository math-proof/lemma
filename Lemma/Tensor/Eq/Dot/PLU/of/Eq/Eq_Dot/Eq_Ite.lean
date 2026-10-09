import sympy.matrices.plu
import sympy.Basic
import Lemma.Matrix.All_Eq_MulPluUndo.of.All_IsUnitDet.All_EqMul_1.All_Eq_Mul.All_Eq_Mul.Eq
open Matrix


/--
Corrected PLU identity. The py conclusion
`X = (∏ₖ Sₖᵀ) (∏ₖ Lₖ) B(n-1)` is false: elimination blocks must be inverted and interleaved
with the swaps. The telescoping form is `X = pluUndo S L m * A m`.
-/
@[path]
private lemma main
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
-- proof
  All_Eq_MulPluUndo.of.All_IsUnitDet.All_EqMul_1.All_Eq_Mul.All_Eq_Mul.Eq h₀ h₁ h₂ h₃ h₄


-- created on 2023-08-19
-- updated on 2026-10-10
