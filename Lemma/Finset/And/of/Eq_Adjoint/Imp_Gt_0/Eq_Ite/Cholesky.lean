import sympy.matrices.cholesky
import sympy.Basic
import Lemma.Matrix.All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef
open Matrix
open scoped ComplexOrder


@[main]
private lemma main
  {n : ℕ}
  {A : Matrix (Fin n) (Fin n) ℂ}
  {L : Matrix (Fin n) (Fin n) ℂ}
-- given
  (h₀ : Aᴴ = A)
  (h₁ : ∀ x : Fin n → ℂ, x ≠ 0 → 0 < star x ⬝ᵥ (A *ᵥ x))
  (h₂ : ∀ i j, L i j = if j < i then (A i j - ∑ k ∈ Finset.Iio j, L i k * star (L j k)) / L j j else if j = i then ((Real.sqrt (RCLike.re (A i i) - ∑ k ∈ Finset.Iio i, ‖L i k‖ ^ 2) : ℝ) : ℂ) else 0) :
-- imply
  A = L * Lᴴ := by
-- proof
  have hA : A.PosDef := Matrix.PosDef.of_dotProduct_mulVec_pos h₀ (fun x hx => h₁ x hx)
  exact (All_Eq_0_And_All_Gt_0_And_Eq_Mul.of.IsCholeskyRec.PosDef hA h₂).2.2


-- created on 2023-05-01
