import Mathlib
import sympy.Basic
import sympy.matrices.inner_product_space.SchurHorn

/--
[SchurHorn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/SchurHorn.lean)
-/
@[path]
private lemma schur_diagonal_eigenvalues_doubly_stochastic_eq
-- given
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  {n : ℕ}
  (T : E →ₗ[ℂ] E)
  (hT : T.IsSymmetric)
  (hn : Module.finrank ℂ E = n)
  (b : OrthonormalBasis (Fin n) ℂ E) :
-- imply
  ∃ D : Matrix (Fin n) (Fin n) ℝ,
    D ∈ doublyStochastic ℝ (Fin n) ∧
      (fun i => RCLike.re (inner (𝕜 := ℂ) (b i) (T (b i))) : Fin n → ℝ) =
        D.mulVec (hT.eigenvalues hn) := by
-- proof
  apply InnerProductSpace.SchurHorn.schur_diagonal_eigenvalues_doublyStochastic T hT hn b

-- created on 2026-10-10
