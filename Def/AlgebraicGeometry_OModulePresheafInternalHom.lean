module
public import Mathlib
public import Def.AlgebraicGeometry_OModulePresheafHom
public import Instance.AlgebraicGeometry_OModulePresheafInternalHom
public import Abbrev.AlgebraicGeometry_OModulePresheafInternalHom
set_option autoImplicit false


public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} (F G : OModulePresheaf π)

def homSub (U : V.Opens) : Submodule R (HomPi F G U) where
  carrier := {φ | (∀ (W : AffBelow U) (a : Γ(V, W.1.1)) (x : F.obj W.1.1), φ W (a • x) = a • φ W x) ∧
    ∀ (W W' : AffBelow U) (h : W.1.1 ≤ W'.1.1) (x : F.obj W'.1.1), φ W (F.res h x) = G.res h (φ W' x)}
  add_mem' {φ ψ} hφ hψ := by
    refine ⟨fun W a x => ?_, fun W W' h x => ?_⟩
    · simp only [Pi.add_apply, LinearMap.add_apply, hφ.1, hψ.1, smul_add]
    · simp only [Pi.add_apply, LinearMap.add_apply, hφ.2 W W' h, hψ.2 W W' h, map_add]
  zero_mem' := ⟨fun W a x => by simp, fun W W' h x => by simp⟩
  smul_mem' r {φ} hφ := by
    refine ⟨fun W a x => ?_, fun W W' h x => ?_⟩
    · simp only [Pi.smul_apply, LinearMap.smul_apply, hφ.1]
      letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1
      rw [← algebraMap_smul (A := Γ(V, W.1.1)) r (a • φ W x), ← algebraMap_smul (A := Γ(V, W.1.1)) r (φ W x),
        smul_smul, smul_smul, mul_comm]
    · simp only [Pi.smul_apply, LinearMap.smul_apply, hφ.2 W W' h, map_smul]

def sectionsSMul (U : V.Opens) (a : Γ(V, U)) (φ : homSub F G U) : homSub F G U :=
  ⟨fun W =>
    { toFun := fun x => (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x
      map_add' := fun x y => by simp only [map_add, smul_add]
      map_smul' := fun c x => by simp only [map_smul, RingHom.id_apply, smul_comm_sections] }, by
    refine ⟨fun W b x => ?_, fun W W' h x => ?_⟩
    · change (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W (b • x) =
        b • ((V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W x)
      rw [φ.2.1, smul_smul, smul_smul, mul_comm]
    · change (V.presheaf.map (homOfLE W.2).op).hom a • φ.1 W (F.res h x) =
        G.res h ((V.presheaf.map (homOfLE W'.2).op).hom a • φ.1 W' x)
      rw [φ.2.2 W W' h, G.res_smul, ← CommRingCat.comp_apply, ← V.presheaf.map_comp]
      rfl⟩

def homRes {U U' : V.Opens} (h : U ≤ U') : homSub F G U' →ₗ[R] homSub F G U where
  toFun φ := ⟨fun W => φ.1 ⟨W.1, W.2.trans h⟩, ⟨fun W a x => φ.2.1 ⟨W.1, W.2.trans h⟩ a x,
    fun W W' hW x => φ.2.2 ⟨W.1, W.2.trans h⟩ ⟨W'.1, W'.2.trans h⟩ hW x⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def internalHom : OModulePresheaf π where
  obj U := homSub F G U
  moduleSections U := moduleSectionsHomSub F G U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    refine ⟨fun r a φ => ?_⟩
    ext W x
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π W.1.1
    have hr : (V.presheaf.map (homOfLE W.2).op).hom (algebraMap R Γ(V, U) r) = algebraMap R Γ(V, W.1.1) r :=
      (Scheme.TwoAffineOpenCover.restrictAlgHom π W.2).commutes r
    simp only [sections_smul_apply, Algebra.smul_def, mul_smul, Submodule.coe_smul, Pi.smul_apply,
      LinearMap.smul_apply, hr, algebraMap_smul]
  res h := homRes F G h
  res_smul h a φ := by
    ext W x
    simp only [homRes_apply, sections_smul_apply]
    congr 1
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]
    rfl
  res_refl U := rfl
  res_comp h h' := rfl

namespace internalHom

def eval {U : V.Opens} (W : V.affineOpens) (hW : W.1 ≤ U) : (internalHom F G).obj U →ₗ[R] (F.obj W.1 →ₗ[R] G.obj W.1) where
  toFun φ := φ.1 ⟨W, hW⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def toAffHom (φ : (internalHom F G).obj ⊤) : AffHom F G where
  app W := φ.1 ⟨W, le_top⟩
  app_smul W a x := φ.2.1 ⟨W, le_top⟩ a x
  naturality {W W'} h := LinearMap.ext fun x => φ.2.2 ⟨W, le_top⟩ ⟨W', le_top⟩ h x

def ofAffHom (ψ : AffHom F G) : (internalHom F G).obj ⊤ :=
  ⟨fun W => ψ.app W.1, ⟨fun W a x => ψ.app_smul W.1 a x, fun _ _ h x => ψ.naturality_apply h x⟩⟩

end internalHom

end OModulePresheaf

end AlgebraicGeometry

end
