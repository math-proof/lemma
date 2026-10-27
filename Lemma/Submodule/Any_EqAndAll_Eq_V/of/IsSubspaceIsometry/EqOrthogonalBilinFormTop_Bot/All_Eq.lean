import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.ExtendingIsometries
import Lemma.Submodule.OfEq.eq.M.of.Eq
import Lemma.Fin.Eq.of.Ne_0.All_Eq
import Def.v1.Atlas.Buildings.code.GeometricAlgebra.WittTheorem.Part2


/--
[isometry_extension_lemma](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/IsometryExtensionLemma.lean)
-/
@[path]
lemma isometry_extension_lemma
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {U W : Submodule k V}
  {φ : U ≃ₗ[k] W}
-- given
  (hBsymm : ∀ x y : V, B x y = B y x)
  (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
  (hφ : Garrett.IsSubspaceIsometry B U W φ) :
-- imply
  ∃ Φ : V ≃ₗ[k] V, (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧ (∀ u : U, Φ (u : V) = (φ u : V)) :=
-- proof
  Garrett.wittExtensionProp_of_symmetric B hBsymm hnd hnd U W φ hφ

/--
[witt_cancellation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/IsometryExtensionLemma.lean)
-/
@[path]
lemma witt_cancellation
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
  {U₁ U₂ : Submodule k V}
  {φ : U₁ ≃ₗ[k] U₂}
-- given
  (hBsymm : ∀ x y : V, B x y = B y x)
  (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥)
  (hφ : Garrett.IsSubspaceIsometry B U₁ U₂ φ) :
-- imply
  ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k] (LinearMap.BilinForm.orthogonal B U₂), Garrett.IsSubspaceIsometry B (LinearMap.BilinForm.orthogonal B U₁) (LinearMap.BilinForm.orthogonal B U₂) ψ :=
-- proof
  Garrett.wittCancellationProp_of_symmetric B hBsymm hnd hnd U₁ U₂ φ hφ

/--
[witt_theorem_section_7_3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/IsometryExtensionLemma.lean)
-/
@[path]
lemma witt_theorem_section_7_3
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  {B : LinearMap.BilinForm k V}
-- given
  (hBsymm : ∀ x y : V, B x y = B y x)
  (hnd : LinearMap.BilinForm.orthogonal B ⊤ = ⊥) :
-- imply
  (∀ (U W : Submodule k V) (φ : U ≃ₗ[k] W), Garrett.IsSubspaceIsometry B U W φ → ∃ Φ : V ≃ₗ[k] V, (∀ v₁ v₂, B (Φ v₁) (Φ v₂) = B v₁ v₂) ∧ (∀ u : U, Φ (u : V) = (φ u : V))) ∧ (∀ (U₁ U₂ : Submodule k V) (φ : U₁ ≃ₗ[k] U₂), Garrett.IsSubspaceIsometry B U₁ U₂ φ → ∃ ψ : (LinearMap.BilinForm.orthogonal B U₁) ≃ₗ[k] (LinearMap.BilinForm.orthogonal B U₂), Garrett.IsSubspaceIsometry B (LinearMap.BilinForm.orthogonal B U₁) (LinearMap.BilinForm.orthogonal B U₂) ψ) :=
-- proof
  ⟨fun U W φ hφ => isometry_extension_lemma B hBsymm hnd U W φ hφ,
    fun U₁ U₂ φ hφ => witt_cancellation B hBsymm hnd U₁ U₂ φ hφ⟩


-- created on 2026-10-23
