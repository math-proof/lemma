import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.CompositionSeries


/--
[stdFiltMult_eq_dimHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/CompositionSeries.lean)
-/
@[path]
private lemma stdFiltMult_eq_dimHom_eq
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  {lam mu : Δ.𝔥 →ₗ[R] R} :
-- imply
  standardFiltrationMultiplicity rd wg lam mu = dimHomProjectiveContragredientVerma R 𝔤 Δ rd wg lam mu := by
-- proof
  apply stdFiltMult_eq_dimHom R 𝔤 rd wg lam mu


-- created on 2026-10-23
-- updated on 2026-10-24
