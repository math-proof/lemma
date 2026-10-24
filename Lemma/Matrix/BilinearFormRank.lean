import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearFormRank
open LinearMap.BilinForm
open MathlibExt.LinearAlgebra.BilinearFormRankWanted


namespace LinearMap.BilinForm

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
/--
[bilinRank_toMatrix_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
private lemma bilinRank_toMatrix_le {n₁ n₂ : Type*} [Fintype n₁] [DecidableEq n₁]
  [Fintype n₂] [DecidableEq n₂] (b₁ : Module.Basis n₁ K V) (b₂ : Module.Basis n₂ K V)
  (B : LinearMap.BilinForm K V) : (toMatrix b₂ B).rank ≤ (toMatrix b₁ B).rank := by
  rw [← toMatrix_mul_basis_toMatrix b₁ b₂ B]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

end LinearMap.BilinForm

namespace LinearMap.BilinForm

/--
[rank_toMatrix_eq_rank_toMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
lemma rank_toMatrix_eq_rank_toMatrix
  [Field K] [AddCommGroup V] [Module K V] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {b₁ : Module.Basis n₁ K V}
  {b₂ : Module.Basis n₂ K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  (toMatrix b₁ B).rank = (toMatrix b₂ B).rank := by
-- proof
  apply le_antisymm
  · exact bilinRank_toMatrix_le b₂ b₁ B
  · exact bilinRank_toMatrix_le b₁ b₂ B
end LinearMap.BilinForm


namespace MathlibExt.LinearAlgebra.BilinearFormRankWanted

/--
[bilinFormRank_eq_matrix_rank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
lemma bilinFormRank_eq_matrix_rank
  [Field K] [AddCommGroup V] [Module K V] [Fintype n] [DecidableEq n]
  {b : Module.Basis n K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  bilinFormRank b B = (LinearMap.BilinForm.toMatrix b B).rank :=
-- proof
  rfl

end MathlibExt.LinearAlgebra.BilinearFormRankWanted

namespace MathlibExt.LinearAlgebra.BilinearFormRankWanted

/--
[bilinFormRank_basis_independent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
lemma bilinFormRank_basis_independent
  [Field K] [AddCommGroup V] [Module K V] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {b₁ : Module.Basis n₁ K V}
  {b₂ : Module.Basis n₂ K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  bilinFormRank b₁ B = (LinearMap.BilinForm.toMatrix b₂ B).rank := by
-- proof
  rw [bilinFormRank_eq_matrix_rank]
  exact LinearMap.BilinForm.rank_toMatrix_eq_rank_toMatrix b₁ b₂ B

end MathlibExt.LinearAlgebra.BilinearFormRankWanted


-- created on 2026-10-20
-- updated on 2026-10-23
