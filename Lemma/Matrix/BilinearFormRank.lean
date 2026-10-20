import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.BilinearFormRank
open LinearMap.BilinForm
open MathlibExt.LinearAlgebra.BilinearFormRankWanted


/--
[rank_toMatrix_eq_rank_toMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
private lemma rank_toMatrix_eq_rank_toMatrix_eq
  [Field K] [AddCommGroup V] [Module K V] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {b₁ : Module.Basis n₁ K V}
  {b₂ : Module.Basis n₂ K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  (toMatrix b₁ B).rank = (toMatrix b₂ B).rank := by
-- proof
  apply LinearMap.BilinForm.rank_toMatrix_eq_rank_toMatrix b₁ b₂ B

/--
[bilinFormRank_eq_matrix_rank](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
private lemma bilinFormRank_eq_matrix_rank_eq
  [Field K] [AddCommGroup V] [Module K V] [Fintype n] [DecidableEq n]
  {b : Module.Basis n K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  bilinFormRank b B = (LinearMap.BilinForm.toMatrix b B).rank := by
-- proof
  apply MathlibExt.LinearAlgebra.BilinearFormRankWanted.bilinFormRank_eq_matrix_rank b B

/--
[bilinFormRank_basis_independent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/BilinearFormRank.lean)
-/
@[path]
private lemma bilinFormRank_basis_independent_eq
  [Field K] [AddCommGroup V] [Module K V] [Fintype n₁] [DecidableEq n₁] [Fintype n₂] [DecidableEq n₂]
  {b₁ : Module.Basis n₁ K V}
  {b₂ : Module.Basis n₂ K V}
  {B : LinearMap.BilinForm K V} :
-- imply
  bilinFormRank b₁ B = (LinearMap.BilinForm.toMatrix b₂ B).rank := by
-- proof
  apply MathlibExt.LinearAlgebra.BilinearFormRankWanted.bilinFormRank_basis_independent b₁ b₂ B


-- created on 2026-10-20
