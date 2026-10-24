import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra
open Module SymplecticLinearAlgebra


namespace SymplecticLinearAlgebra

/--
[IsSymplecticForm.orthogonal_top_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
lemma IsSymplecticForm.orthogonal_top_eq_bot
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  Ω.orthogonal ⊤ = ⊥ :=
-- proof
  LinearMap.BilinForm.orthogonal_top_eq_bot
    ((LinearMap.IsRefl.nondegenerate_iff_separatingLeft hΩ.alt.isRefl).mpr hΩ.nondeg)

end SymplecticLinearAlgebra

/--
[sympl_skew](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
private lemma sympl_skew_eq
  [AddCommGroup V]
  [Module ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {x y : V}
-- given
  (hAlt : Ω.IsAlt) :
-- imply
  Ω x y = -(Ω y x) := by
-- proof
  apply SymplecticLinearAlgebra.sympl_skew hAlt x y

/--
[symplecticOrtho_finrank_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
private lemma symplecticOrtho_finrank_add_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  finrank ℝ ↥E + finrank ℝ ↥(symplecticOrtho Ω E) = finrank ℝ V := by
-- proof
  apply SymplecticLinearAlgebra.symplecticOrtho_finrank_add hΩ E

/--
[symplectic_subspace_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
private lemma symplectic_subspace_iff_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω) :
-- imply
  IsSymplecticSubspace Ω E ↔ IsCompl E (symplecticOrtho Ω E) := by
-- proof
  apply SymplecticLinearAlgebra.symplectic_subspace_iff hΩ E

/--
[lagrangian_half_dim](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
private lemma lagrangian_half_dim_eq
  [AddCommGroup V]
  [Module ℝ V]
  [FiniteDimensional ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V}
-- given
  (hΩ : IsSymplecticForm Ω)
  (hE : IsLagrangian Ω E) :
-- imply
  2 * finrank ℝ ↥E = finrank ℝ V := by
-- proof
  apply SymplecticLinearAlgebra.lagrangian_half_dim hΩ hE

/--
[ker_symplRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticLinearAlgebra.lean)
-/
@[path]
private lemma ker_symplRestrict_eq
  [AddCommGroup V]
  [Module ℝ V]
  {Ω : LinearMap.BilinForm ℝ V}
  {E : Submodule ℝ V} :
-- imply
  LinearMap.ker (symplRestrict Ω E) = Ω.orthogonal E := by
-- proof
  apply SymplecticLinearAlgebra.ker_symplRestrict Ω E


-- created on 2026-10-23
