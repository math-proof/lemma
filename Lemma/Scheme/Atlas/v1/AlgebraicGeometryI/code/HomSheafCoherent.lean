import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.HomSheafCoherent
open HomSheafCoherent


namespace HomSheafCoherent

/--
[hom_module_finite_of_noetherian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HomSheafCoherent.lean)
-/
@[path]
lemma hom_module_finite_of_noetherian
  [CommRing R]
  [IsNoetherianRing R]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [AddCommGroup N]
  [Module R N]
  [Module.Finite R N] :
-- imply
  Module.Finite R (M →ₗ[R] N) := by
-- proof
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  let p : (Fin n → R) →ₗ[R] M := Finsupp.linearCombination R s ∘ₗ
    (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm.toLinearMap
  have hp : Function.Surjective p := by
    rw [← LinearMap.range_eq_top]
    simp only [p, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      Finsupp.range_linearCombination]
    exact hs
  let φ : (M →ₗ[R] N) →ₗ[R] ((Fin n → R) →ₗ[R] N) := LinearMap.lcomp R N p
  have hφ : Function.Injective φ := by
    intro f g h
    ext x
    obtain ⟨y, rfl⟩ := hp x
    exact LinearMap.congr_fun h y
  haveI : IsNoetherian R ((Fin n → R) →ₗ[R] N) := inferInstance
  exact Module.Finite.of_injective φ hφ

end HomSheafCoherent

namespace HomSheafCoherent

/--
[sheafHom_coherent_on_affine](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HomSheafCoherent.lean)
-/
@[path]
lemma sheafHom_coherent_on_affine
  [CommRing R]
  [IsNoetherianRing R]
  {M N : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [AddCommGroup N]
  [Module R N]
  [Module.Finite R N] :
-- imply
  Module.Finite R (M →ₗ[R] N) ∧ ∀ (S : Submonoid R), Nonempty (LocalizedModule S (M →ₗ[R] N) ≃ₗ[R] (LocalizedModule S M →ₗ[R] LocalizedModule S N)) := by
-- proof
  refine ⟨hom_module_finite_of_noetherian M N, fun S => ⟨?_⟩⟩
  exact hom_localization_equiv_noetherian M N S

end HomSheafCoherent


-- created on 2026-10-23
