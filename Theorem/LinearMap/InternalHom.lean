module

public import Mathlib
public import Instance.PresheafOfModules_InternalHom
public import Abbrev.PresheafOfModules_InternalHom

public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


universe u v' u'

open CategoryTheory MonoidalCategory Limits Opposite

namespace PresheafOfModules

section general

variable {C : Type u'} [Category.{v'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F N : PresheafOfModules.{u} (R ⋙ forget₂ _ _))

namespace InternalHom

public theorem map_id_apply (M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) (X : Cᵒᵖ) (x : M.obj X) :
    M.map (𝟙 X) x = x := by
  change (M.presheaf.map (𝟙 X)) x = x
  rw [M.presheaf.map_id]; rfl

variable {F N} in


@[ext] public theorem naturalFamilies_ext {X : Cᵒᵖ} {φ ψ : naturalFamilies F N X}
    (h : ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (x : F.obj Y), φ.1 f x = ψ.1 f x) : φ = ψ :=
  Subtype.ext (funext fun _ => funext fun f => LinearMap.ext (h f))


public theorem naturality {X : Cᵒᵖ} (φ : naturalFamilies F N X) ⦃Y Z : Cᵒᵖ⦄ (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : F.obj Y) : N.map g (φ.1 f x) = φ.1 (f ≫ g) (F.map g x) := φ.2 f g x


public theorem congr_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} {f g : X ⟶ Y} (h : f = g)
    (x : F.obj Y) : φ.1 f x = φ.1 g x := by subst h; rfl


@[simp] public theorem smul_app {X : Cᵒᵖ} (r : R.obj X) (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (r • φ).1 f x = R.map f r • φ.1 f x := rfl

@[simp] public theorem add_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ + ψ).1 f x = φ.1 f x + ψ.1 f x := rfl

@[simp] public theorem zero_app {X : Cᵒᵖ} {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (0 : naturalFamilies F N X).1 f x = 0 := rfl

@[simp] public theorem neg_app {X : Cᵒᵖ} (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (-φ).1 f x = - φ.1 f x := rfl

@[simp] public theorem sub_app {X : Cᵒᵖ} (φ ψ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (φ - ψ).1 f x = φ.1 f x - ψ.1 f x := rfl

variable (F N)


@[simp] public theorem restrict_app {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : (restrict F N h φ).1 f x = φ.1 (h ≫ f) x := rfl


@[simp] public theorem presheaf_map_apply {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : naturalFamilies F N X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) : ((presheaf F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

variable {N} in


@[simp] public theorem postcomp_app {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N') {X : Cᵒᵖ}
    (φ : naturalFamilies F N X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    (postcomp F ψ X φ).1 f x = ψ.app Y (φ.1 f x) := rfl

end InternalHom

open InternalHom


@[simp] public theorem ihomObj_map_val {X X' : Cᵒᵖ} (h : X ⟶ X') (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ}
    (f : X' ⟶ Y) (x : F.obj Y) :
    ((ihomObj F N).map h φ).1 f x = φ.1 (h ≫ f) x := rfl

variable {N} in


@[simp] public theorem ihomMap_app_val {N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N ⟶ N')
    {X : Cᵒᵖ} (φ : (ihomObj F N).obj X) {Y : Cᵒᵖ} (f : X ⟶ Y) (x : F.obj Y) :
    ((ihomMap F ψ).app X φ).1 f x = ψ.app Y (φ.1 f x) := rfl


@[simp] public theorem ihomFunctor_obj (N' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (ihomFunctor F).obj N' = ihomObj F N' := rfl

@[simp] public theorem ihomFunctor_map {N' N'' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} (ψ : N' ⟶ N'') :
    (ihomFunctor F).map ψ = ihomMap F ψ := rfl

end general

section closed

variable {C : Type u} [Category.{u} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
  (F : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) {G N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}

namespace InternalHom


@[simp] public theorem curryFamily_app (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : (curryFamily F θ y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl

end InternalHom

open InternalHom


@[simp] public theorem curry'_app_val (θ : F ⊗ G ⟶ N) {X : Cᵒᵖ} (y : G.obj X) {Y : Cᵒᵖ} (f : X ⟶ Y)
    (x : F.obj Y) : ((curry' F θ).app X y).1 f x = θ.app Y (x ⊗ₜ[R.obj Y] G.map f y) := rfl


public theorem tensorObj_map_tmul' {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :))
      (β := fun _ => (ModuleCat.restrictScalars (R.map g).hom).obj (F.obj Y ⊗ G.obj Y))
      (ModuleCat.Hom.hom (R := ↑(R.obj X)) ((F ⊗ G).map g)) (x ⊗ₜ[R.obj X] y) =
    F.map g x ⊗ₜ[R.obj Y] G.map g y := rfl


public theorem uncurryApp_tmul (κ : G ⟶ ihomObj F N) (X : Cᵒᵖ) (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      (uncurryApp F κ X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x := by
  erw [ModuleCat.MonoidalCategory.tensorLift_tmul]


public theorem uncurry'_app_tmul (κ : G ⟶ ihomObj F N) {X : Cᵒᵖ} (x : F.obj X) (y : G.obj X) :
    DFunLike.coe (α := (F.obj X ⊗ G.obj X :)) (β := fun _ => N.obj X)
      ((uncurry' F κ).app X).hom (x ⊗ₜ[R.obj X] y) = (κ.app X y).1 (𝟙 X) x :=
  uncurryApp_tmul F κ X x y


public theorem uncurry'_curry' (θ : F ⊗ G ⟶ N) : uncurry' F (curry' F θ) = θ := by
  ext X : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  erw [uncurry'_app_tmul]
  change θ.app X (x ⊗ₜ[R.obj X] G.map (𝟙 X) y) = θ.app X (x ⊗ₜ[R.obj X] y)
  rw [InternalHom.map_id_apply]


public theorem curry'_uncurry' (κ : G ⟶ ihomObj F N) : curry' F (uncurry' F κ) = κ := by
  ext X y
  apply naturalFamilies_ext; intro Y f x
  rw [curry'_app_val]
  erw [uncurry'_app_tmul]
  rw [naturality_apply κ f y, ihomObj_map_val]
  exact congr_app _ (by simp) _

