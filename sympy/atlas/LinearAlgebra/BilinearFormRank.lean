/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank of a bilinear form

This file proves that the rank of the matrix of a bilinear form is independent of the chosen
basis.
-/

namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

private theorem bilinRank_toMatrix_le {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V)
    (B : LinearMap.BilinForm K V) : (toMatrix b₂ B).rank ≤ (toMatrix b₁ B).rank := by
  rw [← toMatrix_mul_basis_toMatrix b₁ b₂ B]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

/-- The rank of the matrix of a bilinear form is independent of the chosen basis. -/
theorem rank_toMatrix_eq_rank_toMatrix {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂] (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V)
    (B : LinearMap.BilinForm K V) : (toMatrix b₁ B).rank = (toMatrix b₂ B).rank := by
  apply le_antisymm
  · exact bilinRank_toMatrix_le b₂ b₁ B
  · exact bilinRank_toMatrix_le b₁ b₂ B

end LinearMap.BilinForm

namespace MathlibExt.LinearAlgebra.BilinearFormRankWanted

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
The rank of a bilinear form: the rank of its Gram matrix in any basis.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
noncomputable def bilinFormRank {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K V) (B : LinearMap.BilinForm K V) : ℕ :=
  (LinearMap.BilinForm.toMatrix b B).rank

/--
Characteristic property: the rank of a bilinear form is the rank of its matrix in the given
basis.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.
-/
theorem bilinFormRank_eq_matrix_rank {n : Type*} [Fintype n] [DecidableEq n]
    (b : Module.Basis n K V) (B : LinearMap.BilinForm K V) :
    bilinFormRank b B = (LinearMap.BilinForm.toMatrix b B).rank := rfl

/--
The rank of a bilinear form does not depend on the choice of basis.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Bilinear forms / rank of a bilinear form; N. Bourbaki, Algebra I, Chapters 1-3, Springer (1989),
Chapter III.

Proves `Wanted` entry `bilinFormRank_basis_independent`.

Proof: Express one Gram matrix as a two-sided change-of-basis product. The two matrix-rank
multiplication inequalities give both rank inequalities, hence equality.
-/
theorem bilinFormRank_basis_independent {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
    [Fintype n₂] [DecidableEq n₂]
    (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V) (B : LinearMap.BilinForm K V) :
    bilinFormRank b₁ B = (LinearMap.BilinForm.toMatrix b₂ B).rank := by
  rw [bilinFormRank_eq_matrix_rank]
  exact LinearMap.BilinForm.rank_toMatrix_eq_rank_toMatrix b₁ b₂ B

end MathlibExt.LinearAlgebra.BilinearFormRankWanted
