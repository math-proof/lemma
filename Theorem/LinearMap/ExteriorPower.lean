module

public import Mathlib
public import Instance.PresheafOfModules_ExteriorPower

public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


universe u

open CategoryTheory
namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

section map
variable {X Y : Cᵒᵖ} (f : X ⟶ Y)


public theorem mapₗ_ιMulti (m : Fin n → M.obj X) :
    mapₗ n M f (exteriorPower.ιMulti (R.obj X) n m) = exteriorPower.ιMulti (R.obj Y) n (M := M.obj Y) (fun i => M.map f (m i)) := by
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  simp [mapₗ]
  rfl


public theorem mapₗ_smul (r : R.obj X) (x : ⋀[R.obj X]^n (M.obj X)) :
    mapₗ n M f (r • x) = R.map f r • mapₗ n M f x := by
  letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exact (mapₗ n M f).map_smul r x

end map


public theorem addMonoidHom_ext {X : Cᵒᵖ} {N : Type*} [AddCommGroup N] {φ ψ : ⋀[R.obj X]^n (M.obj X) →+ N}
    (hsmul : ∀ (r : R.obj X) x, φ x = ψ x → φ (r • x) = ψ (r • x))
    (h : ∀ m : Fin n → M.obj X, φ (exteriorPower.ιMulti (R.obj X) n m) = ψ (exteriorPower.ιMulti (R.obj X) n m)) :
    φ = ψ := by
  ext x
  have hx : x ∈ Submodule.span (R.obj X) (Set.range (exteriorPower.ιMulti (R.obj X) n (M := M.obj X))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨m, rfl⟩ := hx; exact h m
  | zero => simp
  | add x y _ _ hx hy => simp [hx, hy]
  | smul r x _ hx => exact hsmul r x hx


@[simp] public theorem exteriorPower_map_ιMulti (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : Fin n → M.obj X) :
    ((exteriorPower n M).map f (show (exteriorPower n M).obj X from exteriorPower.ιMulti (R.obj X) n m) :
        ⋀[R.obj Y]^n (M.obj Y)) = exteriorPower.ιMulti (R.obj Y) n (M := M.obj Y) (fun i => M.map f (m i)) :=
  ExteriorPower.mapₗ_ιMulti n M f m

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}


@[simp] public theorem appₗ_apply (φ : M ⟶ N) (X : Cᵒᵖ) (x : M.obj X) : appₗ φ X x = φ.app X x := rfl


public theorem appₗ_id (X : Cᵒᵖ) : appₗ (𝟙 M) X = LinearMap.id := rfl


public theorem appₗ_comp (φ : M ⟶ N) (ψ : N ⟶ P) (X : Cᵒᵖ) :
    appₗ (φ ≫ ψ) X = appₗ ψ X ∘ₗ appₗ φ X := rfl


public theorem exteriorPowerMap_app_apply (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (x : ⋀[R.obj X]^n (M.obj X)) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from x) : ⋀[R.obj X]^n (N.obj X)) =
      exteriorPower.map n (ExteriorPower.appₗ φ X) x := rfl


public theorem exteriorPowerMap_app_ιMulti (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) (X : Cᵒᵖ) (m : Fin n → M.obj X) :
    ((exteriorPowerMap n φ).app X (show (exteriorPower n M).obj X from exteriorPower.ιMulti (R.obj X) n m) :
      ⋀[R.obj X]^n (N.obj X)) = exteriorPower.ιMulti (R.obj X) n (fun i => φ.app X (m i)) :=
  exteriorPower.map_apply_ιMulti _ _

variable (R) in

