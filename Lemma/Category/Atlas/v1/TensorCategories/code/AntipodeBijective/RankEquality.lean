import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.HopfAlgebra
import Lemma.Category.Atlas.v1.TensorCategories.code.HopfAlgebra
open Function


namespace HopfAlgebra

/--
[antipode_rank_eq_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/AntipodeBijective/RankEquality.lean)
-/
@[path]
lemma antipode_rank_eq_dim
  {K : Type*}
  [Field K]
  {H : Type*}
  [Ring H]
  [HopfAlgebra K H]
  [FiniteDimensional K H] :
-- imply
  LinearMap.rank (HopfAlgebra.antipode K : H →ₗ[K] H) = Module.rank K H :=
-- proof
  rank_range_of_surjective _ (HopfAlgebra.antipode_bijective K H).2

end HopfAlgebra


-- created on 2026-10-23
