import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.GeometricAlgebra.WittCancellationDirectSum
open Garrett


/--
[extractEquiv_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean)
-/
@[path]
private lemma main
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup U]
  [Module k U]
  [FiniteDimensional k U]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  [AddCommGroup W]
  [Module k W]
  [FiniteDimensional k W]
  {B_U : LinearMap.BilinForm k U}
  {B_V : LinearMap.BilinForm k V}
  {B_W : LinearMap.BilinForm k W}
  {Ψ : (U × V) ≃ₗ[k] (U × W)}
-- given
  (hU_nd : IsNondegenerate' B_U)
  (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
  (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0)) :
-- imply
  IsFormedSpaceIso B_V B_W (extractEquiv B_U B_V B_W hU_nd Ψ hΨ hΨ_U) := by
-- proof
  intro v₁ v₂
  show B_W (Ψ (0, v₁)).2 (Ψ (0, v₂)).2 = B_V v₁ v₂
  have hfst := first_component_zero B_U B_V B_W hU_nd Ψ hΨ hΨ_U
  have key := hΨ (0, v₁) (0, v₂)
  simp [orthogonalSumForm_apply] at key
  rw [hfst v₁, hfst v₂] at key
  simp at key
  exact key
/-- Witt cancellation for orthogonal direct sums: if `U ⊕ V` is isometric to
`U ⊕ W` (with the same nondegenerate `U`-summand), then `V` is isometric to `W`. -/


/--
[orthogonalSumForm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean)
-/
private lemma orthogonalSumForm_apply_eq
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup U]
  [Module k U]
  [AddCommGroup W]
  [Module k W]
  {B_U : LinearMap.BilinForm k U}
  {B_W : LinearMap.BilinForm k W}
  {x y : U × W} :
-- imply
  orthogonalSumForm B_U B_W x y = B_U x.1 y.1 + B_W x.2 y.2 := by
-- proof
  apply Garrett.orthogonalSumForm_apply B_U B_W x y

/--
[first_component_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/WittCancellationDirectSum.lean)
-/
private lemma first_component_zero_eq
  [Field k]
  [NeZero (2 : k)]
  [AddCommGroup U]
  [Module k U]
  [FiniteDimensional k U]
  [AddCommGroup V]
  [Module k V]
  [FiniteDimensional k V]
  [AddCommGroup W]
  [Module k W]
  [FiniteDimensional k W]
  {B_U : LinearMap.BilinForm k U}
  {B_V : LinearMap.BilinForm k V}
  {B_W : LinearMap.BilinForm k W}
  {Ψ : (U × V) ≃ₗ[k] (U × W)}
  {v : V}
-- given
  (hU_nd : IsNondegenerate' B_U)
  (hΨ : IsFormedSpaceIso (orthogonalSumForm B_U B_V) (orthogonalSumForm B_U B_W) Ψ)
  (hΨ_U : ∀ u : U, Ψ (u, 0) = (u, 0)) :
-- imply
  (Ψ (0, v)).1 = 0 := by
-- proof
  apply Garrett.first_component_zero B_U B_V B_W hU_nd Ψ hΨ hΨ_U v


-- created on 2026-10-23
-- updated on 2026-10-24
