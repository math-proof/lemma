import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section30.Part4
open Matrix SymmetricBilinearForms SurfacesAndBilinearForms BilinearForm
open CategoryTheory AlgebraicTopology LinearMap SingularCohomology
open CategoryTheory AlgebraicTopology SingularCohomology
open LinearMap.BilinForm


namespace SymmetricBilinearForms

/--
[hyperbolicPlusIdentity_matrixCongruent_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
lemma hyperbolicPlusIdentity_matrixCongruent_one
-- imply
  MatrixCongruent hyperbolicPlusIdentity (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
-- proof
  refine ⟨!![1, 1, 1; 1, 0, 1; 0, 1, 1], ?_, ?_⟩
  ·
    decide
  ·
    decide
end SymmetricBilinearForms
namespace AlgebraicTopologyI


namespace SurfacesAndBilinearForms

/--
[connectedSum_mv_restrictionMap₀_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
the image of `H⁰(S₁∖B) ⊕ H⁰(S₂∖B) → H⁰(S¹)` equals the kernel of `δ⁰`. -/
lemma connectedSum_mv_restrictionMap₀_surjective (S₁ S₂ : CompactSurface) :
  Function.Surjective (connectedSum_mv_restrictionMap₀ S₁ S₂) := by
  intro x
  exact ⟨(x, 0), by simp [connectedSum_mv_restrictionMap₀]⟩

end SurfacesAndBilinearForms

namespace BilinearForm

/--
[restrict_nondegenerate_iff_disjoint_orthogonal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
lemma restrict_nondegenerate_iff_disjoint_orthogonal
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {W : Submodule K V}
-- given
  (hB_refl : B.IsRefl) :
-- imply
  (B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W) := by
-- proof
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
    isCompl_orthogonal_iff_disjoint hB_refl]

end BilinearForm

namespace BilinearForm

/--
[restrict_orthogonal_nondegenerate](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
lemma restrict_orthogonal_nondegenerate
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {W : Submodule K V}
-- given
  (hB : B.Nondegenerate)
  (hB_refl : B.IsRefl)
  (hW : (B.restrict W).Nondegenerate) :
-- imply
  (B.restrict (B.orthogonal W)).Nondegenerate := by
-- proof
  rw [restrict_nondegenerate_iff_isCompl_orthogonal hB_refl,
    orthogonal_orthogonal hB hB_refl W]
  exact (isCompl_orthogonal_of_restrict_nondegenerate hB_refl hW).symm

end BilinearForm

namespace BilinearForm

/--
[orthogonalProdEquiv_respects_form](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
lemma orthogonalProdEquiv_respects_form
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {W : Submodule K V}
  {x y : ↥W × ↥(B.orthogonal W)}
-- given
  (hB_refl : B.IsRefl)
  (hW : (B.restrict W).Nondegenerate) :
-- imply
  B (orthogonalProdEquiv B hB_refl hW x) (orthogonalProdEquiv B hB_refl hW y) = B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2) := by
-- proof
  simp only [orthogonalProdEquiv, Submodule.coe_prodEquivOfIsCompl',
    map_add, LinearMap.add_apply]
  have h1 : B (↑x.1) (↑y.2) = 0 := (y.2).2 x.1 (x.1).2
  have h2 : B (↑x.2) (↑y.1) = 0 := hB_refl _ _ ((x.2).2 y.1 (y.1).2)
  simp [h1, h2]

end BilinearForm

namespace BilinearForm

/--
[restrict_nondegenerate_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
lemma restrict_nondegenerate_characterization
  [Field K]
  [AddCommGroup V]
  [Module K V]
  [FiniteDimensional K V]
  {B : LinearMap.BilinForm K V}
  {W : Submodule K V}
-- given
  (hB : B.Nondegenerate)
  (hB_refl : B.IsRefl) :
-- imply
  ((B.restrict W).Nondegenerate ↔ Disjoint W (B.orthogonal W)) ∧ ((B.restrict W).Nondegenerate → (B.restrict (B.orthogonal W)).Nondegenerate) ∧ ((B.restrict W).Nondegenerate → ∃ (e : (↥W × ↥(B.orthogonal W)) ≃ₗ[K] V), ∀ (x y : ↥W × ↥(B.orthogonal W)), B (e x) (e y) = B (↑x.1) (↑y.1) + B (↑x.2) (↑y.2)) :=
-- proof
  ⟨restrict_nondegenerate_iff_disjoint_orthogonal B hB_refl W,
    fun hW => restrict_orthogonal_nondegenerate B hB hB_refl hW,
    fun hW => ⟨orthogonalProdEquiv B hB_refl hW,
      orthogonalProdEquiv_respects_form B hB_refl hW⟩⟩
end BilinearForm
end


/--
[connectedSum_mv_restrictionMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean)
-/
@[path]
private lemma connectedSum_mv_restrictionMap_eq
  {S₁ S₂ : CompactSurface} :
-- imply
  Function.Surjective (connectedSum_mv_restrictionMap₀ S₁ S₂) := by
-- proof
  apply SurfacesAndBilinearForms.connectedSum_mv_restrictionMap S₁ S₂


-- created on 2026-10-23
