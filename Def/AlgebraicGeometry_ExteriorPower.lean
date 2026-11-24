module
public import Mathlib
public import Instance.PresheafOfModules_ExteriorPower
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


public section

universe u

open CategoryTheory
namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))

section map
variable {X Y : Cᵒᵖ} (f : X ⟶ Y)

@[reducible] noncomputable def moduleAlong (R : Cᵒᵖ ⥤ CommRingCat.{u}) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (N : Type u) [AddCommGroup N] [Module (R.obj Y) N] : Module (R.obj X) N :=
  Module.compHom N (R.map f).hom

noncomputable def mapAlong :
    letI := moduleAlong R f (M.obj Y)
    M.obj X →ₗ[R.obj X] M.obj Y :=
  letI := moduleAlong R f (M.obj Y)
  { toFun := fun x => (M.map f x : M.obj Y)
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => M.map_smul f r x }

noncomputable def ιMultiAlong :
    letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    (M.obj Y) [⋀^Fin n]→ₗ[R.obj X] (⋀[R.obj Y]^n (M.obj Y)) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  letI : Algebra (R.obj X) (R.obj Y) := (R.map f).hom.toAlgebra
  haveI : IsScalarTower (R.obj X) (R.obj Y) (M.obj Y) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower (R.obj X) (R.obj Y) (⋀[R.obj Y]^n (M.obj Y)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { (exteriorPower.ιMulti (R.obj Y) n).toMultilinearMap.restrictScalars (R.obj X) with
    map_eq_zero_of_eq' := fun v _ _ h hij => (exteriorPower.ιMulti (R.obj Y) n).map_eq_zero_of_eq v h hij }

noncomputable def mapₗ :
    letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
    ⋀[R.obj X]^n (M.obj X) →ₗ[R.obj X] ⋀[R.obj Y]^n (M.obj Y) :=
  letI := moduleAlong R f (M.obj Y); letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y))
  exteriorPower.alternatingMapLinearEquiv ((ιMultiAlong n M f).compLinearMap (mapAlong M f))

end map

noncomputable def presheafAb : Cᵒᵖ ⥤ Ab.{u} where
  obj X := AddCommGrpCat.of (⋀[R.obj X]^n (M.obj X))
  map {X Y} f := AddCommGrpCat.ofHom (letI := moduleAlong R f (⋀[R.obj Y]^n (M.obj Y)); (mapₗ n M f).toAddMonoidHom)
  map_id X := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (𝟙 X) (r • x) = r • x
      rw [mapₗ_smul, R.map_id]; exact congrArg (r • ·) hx
    · change mapₗ n M (𝟙 X) _ = exteriorPower.ιMulti (R.obj X) n m
      rw [mapₗ_ιMulti]
      congr 1; funext i
      rw [M.map_id]
      rfl
  map_comp {X Y Z} f g := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change mapₗ n M (f ≫ g) (r • x) = mapₗ n M g (mapₗ n M f (r • x))
      rw [mapₗ_smul, mapₗ_smul, mapₗ_smul, R.map_comp]; exact congrArg (_ • ·) hx
    · change mapₗ n M (f ≫ g) _ = mapₗ n M g (mapₗ n M f _)
      rw [mapₗ_ιMulti, mapₗ_ιMulti, mapₗ_ιMulti]
      congr 1; funext i
      exact M.map_comp_apply f g (m i)

end ExteriorPower

noncomputable def exteriorPower (n : ℕ) (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) :=
  @ofPresheaf C _ (R ⋙ forget₂ CommRingCat RingCat) (ExteriorPower.presheafAb n M)
    (fun X => ExteriorPower.instModulePresheafAb n M X)
    (fun _ _ f r x => by
      change ExteriorPower.mapₗ n M f (r • x) = R.map f r • ExteriorPower.mapₗ n M f x
      exact ExteriorPower.mapₗ_smul n M f r x)

end PresheafOfModules

namespace PresheafOfModules

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

namespace ExteriorPower

variable (n : ℕ) {M N P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}

noncomputable def appₗ (φ : M ⟶ N) (X : Cᵒᵖ) : M.obj X →ₗ[R.obj X] N.obj X where
  toFun x := φ.app X x
  map_add' x y := map_add (φ.app X).hom x y
  map_smul' r x := (φ.app X).hom.map_smul r x

noncomputable def mapAb (φ : M ⟶ N) : presheafAb n M ⟶ presheafAb n N where
  app X := AddCommGrpCat.ofHom (exteriorPower.map n (appₗ φ X)).toAddMonoidHom
  naturality {X Y} f := by
    ext1
    refine addMonoidHom_ext n M (fun r x hx => ?_) (fun m => ?_)
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f x) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) x) at hx
      change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (r • x)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (r • x))
      rw [mapₗ_smul, map_smul, map_smul, mapₗ_smul]
      exact congrArg (R.map f r • ·) hx
    · change exteriorPower.map n (appₗ φ Y) (mapₗ n M f (exteriorPower.ιMulti _ n m)) =
        mapₗ n N f (exteriorPower.map n (appₗ φ X) (exteriorPower.ιMulti _ n m))
      rw [mapₗ_ιMulti, exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, mapₗ_ιMulti]
      congr 1
      funext i
      exact naturality_apply φ f (m i)

end ExteriorPower

noncomputable def exteriorPowerMap (n : ℕ) {M N : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)}
    (φ : M ⟶ N) : exteriorPower n M ⟶ exteriorPower n N :=
  homMk (ExteriorPower.mapAb n φ) (fun X r m =>
    (exteriorPower.map n (ExteriorPower.appₗ φ X)).map_smul (show R.obj X from r) m)

variable (R) in

noncomputable def exteriorPowerFunctor (n : ℕ) :
    PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) ⥤
      PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat) where
  obj M := exteriorPower n M
  map φ := exteriorPowerMap n φ
  map_id M := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (𝟙 M) X) x = x
    rw [ExteriorPower.appₗ_id, exteriorPower.map_id]
    rfl
  map_comp φ ψ := by
    ext X : 1
    ext1
    refine LinearMap.ext fun x => ?_
    change exteriorPower.map n (ExteriorPower.appₗ (φ ≫ ψ) X) x =
      exteriorPower.map n (ExteriorPower.appₗ ψ X) (exteriorPower.map n (ExteriorPower.appₗ φ X) x)
    rw [ExteriorPower.appₗ_comp, exteriorPower.map_comp]
    rfl

end PresheafOfModules


-- created on 2026-10-24
-- updated on 2026-11-14
