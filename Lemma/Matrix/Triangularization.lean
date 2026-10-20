import Mathlib
import sympy.Basic
import sympy.atlas.LinearAlgebra.Triangularization
open Polynomial
open MathlibExt.LinearAlgebra.TriangularizationWanted


/--
[exists_basis_upperTriangular_toMatrix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
private lemma exists_basis_upperTriangular_toMatrix_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  {f : Module.End K V}
-- given
  (h : f.charpoly.Splits)
  (hdim : Module.finrank K V = Fintype.card ι) :
-- imply
  ∃ b : Module.Basis ι K V, (LinearMap.toMatrix b b f).IsUpperTriangular := by
-- proof
  apply MathlibExt.LinearAlgebra.TriangularizationWanted.exists_basis_upperTriangular_toMatrix f h hdim

/--
[exists_upperTriangular_similar_of_splits](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Triangularization.lean)
-/
@[path]
private lemma exists_upperTriangular_similar_of_splits_eq
  [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Fintype n] [DecidableEq n] [LinearOrder n]
  {A : Matrix n n K}
-- given
  (h : A.charpoly.Splits) :
-- imply
  ∃ P T : Matrix n n K, IsUnit P ∧ T.IsUpperTriangular ∧ A = P * T * P⁻¹ := by
-- proof
  apply MathlibExt.LinearAlgebra.TriangularizationWanted.exists_upperTriangular_similar_of_splits A h


-- created on 2026-10-20
