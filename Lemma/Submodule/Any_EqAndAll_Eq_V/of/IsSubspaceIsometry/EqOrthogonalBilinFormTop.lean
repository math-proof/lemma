import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries


/--
[wittExtension_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittExtensionProof.lean)
-/
@[path]
private lemma main
  [CommRing k]
  [AddCommGroup V]
  [Module k V]
  {B : LinearMap.BilinForm k V}
  {W : Submodule k V}
  {φ : (⊥ : Submodule k V) ≃ₗ[k] W}
-- given
  (_ : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
  (_ : Garrett.IsSubspaceIsometry B ⊥ W φ) :
-- imply
  ∃ Φ : V ≃ₗ[k] V, (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧ (∀ u : (⊥ : Submodule k V), Φ (u : V) = (φ u : V)) := by
-- proof
  refine ⟨LinearEquiv.refl k V, fun v₁ v₂ => rfl, fun u => ?_⟩
  simp only [LinearEquiv.refl_apply]
  have hu0 : u = 0 := Subtype.ext ((Submodule.mem_bot k).mp u.2)
  subst hu0
  simp [map_zero]


-- created on 2026-10-23
-- updated on 2026-10-24
