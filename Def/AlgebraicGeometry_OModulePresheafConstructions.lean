module
public import Mathlib
public import Def.AlgebraicGeometry_OModulePresheafHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Properties
public import Instance.AlgebraicGeometry_OModulePresheafConstructions
public import Structure.AlgebraicGeometry_OModulePresheafConstructions
public import Abbrev.AlgebraicGeometry_OModulePresheafConstructions
set_option autoImplicit false


public section

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover

def preimage {Z : Scheme.{u}} (i : Z ⟶ V) [IsClosedImmersion i] (K : V.OrderedAffineCover) :
    Z.OrderedAffineCover where
  ι := K.ι
  U j := i ⁻¹ᵁ K.U j
  isAffineOpen j := (K.isAffineOpen j).preimage i
  iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top i K.iSup_eq_top

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}

def prod (F G : OModulePresheaf π) : OModulePresheaf π where
  obj U := F.obj U × G.obj U
  moduleSections U := Prod.instModule
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a x => Prod.ext (smul_assoc r a x.1) (smul_assoc r a x.2)⟩
  res h := (F.res h).prodMap (G.res h)
  res_smul h a x := Prod.ext (F.res_smul h a x.1) (G.res_smul h a x.2)
  res_refl U := LinearMap.ext fun x =>
    Prod.ext (LinearMap.congr_fun (F.res_refl U) x.1) (LinearMap.congr_fun (G.res_refl U) x.2)
  res_comp h h' := LinearMap.ext fun x =>
    Prod.ext (LinearMap.congr_fun (F.res_comp h h') x.1) (LinearMap.congr_fun (G.res_comp h h') x.2)

def fstHom (F G : OModulePresheaf π) : Hom (F.prod G) F := ⟨fun U => LinearMap.fst R _ _, fun _ _ _ => rfl, fun _ => rfl⟩

def sndHom (F G : OModulePresheaf π) : Hom (F.prod G) G := ⟨fun U => LinearMap.snd R _ _, fun _ _ _ => rfl, fun _ => rfl⟩

def pow (F : OModulePresheaf π) (n : ℕ) : OModulePresheaf π where
  obj U := Fin n → F.obj U
  moduleSections U := Pi.module _ _ _
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a x => funext fun j => smul_assoc r a (x j)⟩
  res h := LinearMap.compLeft (F.res h) (Fin n)
  res_smul h a x := funext fun j => F.res_smul h a (x j)
  res_refl U := LinearMap.ext fun x => funext fun j => LinearMap.congr_fun (F.res_refl U) (x j)
  res_comp h h' := LinearMap.ext fun x => funext fun j => LinearMap.congr_fun (F.res_comp h h') (x j)

variable (π) in

def zero : OModulePresheaf π where
  obj _ := PUnit.{u + 1}
  moduleSections _ := inferInstance
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun _ _ _ => Subsingleton.elim _ _⟩
  res _ := 0
  res_smul _ _ _ := Subsingleton.elim _ _
  res_refl _ := Subsingleton.elim _ _
  res_comp _ _ := Subsingleton.elim _ _

def restrOpen (F : OModulePresheaf π) (W₀ : V.Opens) : OModulePresheaf π where
  obj U := F.obj (U ⊓ W₀)
  moduleSections U := Module.compHom _ (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π (U ⊓ W₀)
    letI : Module Γ(V, U) (F.obj (U ⊓ W₀)) :=
      Module.compHom _ (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
    refine ⟨fun r a x => ?_⟩
    show (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom (r • a) • x
      = r • ((V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom a • x)
    rw [Algebra.smul_def, map_mul, mul_smul,
      show (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom (algebraMap R Γ(V, U) r)
        = algebraMap R Γ(V, U ⊓ W₀) r from (Scheme.TwoAffineOpenCover.restrictAlgHom π inf_le_left).commutes r,
      algebraMap_smul]
  res h := F.res (inf_le_inf_right W₀ h)
  res_smul {U U'} h a x := by
    show F.res _ ((V.presheaf.map (homOfLE (inf_le_left : U' ⊓ W₀ ≤ U')).op).hom a • x)
      = (V.presheaf.map (homOfLE (inf_le_left : U ⊓ W₀ ≤ U)).op).hom
          ((V.presheaf.map (homOfLE h).op).hom a) • F.res (inf_le_inf_right W₀ h) x
    rw [F.res_smul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (g := V.presheaf.map _),
      ← V.presheaf.map_comp, ← V.presheaf.map_comp]
    rfl
  res_refl U := F.res_refl (U ⊓ W₀)
  res_comp h h' := F.res_comp (inf_le_inf_right W₀ h) (inf_le_inf_right W₀ h')

section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)

@[reducible] def submoduleSections (U : V.Opens) {M : OModulePresheaf π} (p : Submodule R (M.obj U))
    (hp : ∀ (a : Γ(V, U)) (x : M.obj U), x ∈ p → a • x ∈ p) : Module Γ(V, U) p :=
  letI : SMul Γ(V, U) p := ⟨fun a x => ⟨a • x.1, hp a x.1 x.2⟩⟩
  Function.Injective.module Γ(V, U) ⟨⟨Subtype.val, rfl⟩, fun _ _ => rfl⟩ Subtype.val_injective (fun _ _ => rfl)

def ker : OModulePresheaf π where
  obj U := LinearMap.ker (φ.app U)
  moduleSections U := submoduleSections U _ (ker_smul_mem φ U)
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := submoduleSections U _ (ker_smul_mem φ U)
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res h := (F.res h).restrict fun x hx => LinearMap.mem_ker.mpr <|
    (φ.naturality_apply h x).trans ((congrArg (G.res h) (LinearMap.mem_ker.mp hx)).trans (map_zero _))
  res_smul h a x := Subtype.ext (F.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_refl U) x.1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (F.res_comp h h') x.1)

def im : OModulePresheaf π where
  obj U := LinearMap.range (φ.app U)
  moduleSections U := submoduleSections U _ (range_smul_mem φ U)
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := submoduleSections U _ (range_smul_mem φ U)
    exact ⟨fun r a x => Subtype.ext (smul_assoc r a x.1)⟩
  res h := (G.res h).restrict fun x ⟨s, hs⟩ => ⟨F.res h s, hs ▸ φ.naturality_apply h s⟩
  res_smul h a x := Subtype.ext (G.res_smul h a x.1)
  res_refl U := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_refl U) x.1)
  res_comp h h' := LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun (G.res_comp h h') x.1)

@[reducible] def cokerModuleSections (U : V.Opens) : Module Γ(V, U) (G.obj U ⧸ LinearMap.range (φ.app U)) :=
  letI : SMul Γ(V, U) (G.obj U ⧸ LinearMap.range (φ.app U)) :=
    ⟨fun a => Quotient.map' (a • ·) fun x y hxy => (Submodule.quotientRel_def _).mpr <| by
      rw [← smul_sub]; exact range_smul_mem φ U a _ ((Submodule.quotientRel_def _).mp hxy)⟩
  Function.Surjective.module Γ(V, U) ⟨⟨Submodule.Quotient.mk, rfl⟩, fun _ _ => rfl⟩
    (Submodule.Quotient.mk_surjective _) (fun _ _ => rfl)

def coker : OModulePresheaf π where
  obj U := G.obj U ⧸ LinearMap.range (φ.app U)
  moduleSections U := cokerModuleSections φ U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := cokerModuleSections φ U
    exact ⟨fun r a => Quotient.ind' fun x => congrArg Submodule.Quotient.mk (smul_assoc r a x)⟩
  res {U U'} h := Submodule.mapQ _ _ (G.res h) fun x ⟨s, hs⟩ => ⟨F.res h s, hs ▸ φ.naturality_apply h s⟩
  res_smul {U U'} h a z := z.inductionOn' fun x => congrArg Submodule.Quotient.mk (G.res_smul h a x)
  res_refl U := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (G.res_refl U) x)
  res_comp {U U' U''} h h' := LinearMap.ext fun z => z.inductionOn' fun x =>
    congrArg Submodule.Quotient.mk (LinearMap.congr_fun (G.res_comp h h') x)

def kerImSES : SES (ker φ) F (im φ) where
  inc := { app := fun U => (LinearMap.ker (φ.app U)).subtype, app_smul := fun _ _ _ => rfl, naturality := fun _ => rfl }
  proj := { app := fun U => (φ.app U).rangeRestrict
            app_smul := fun U a x => Subtype.ext (φ.app_smul U a x)
            naturality := fun h => LinearMap.ext fun x => Subtype.ext (φ.naturality_apply h x) }
  injective _ := Subtype.val_injective
  surjective U := LinearMap.surjective_rangeRestrict (φ.app U)
  exact U := (Submodule.range_subtype _).trans (LinearMap.ker_rangeRestrict (φ.app U)).symm

def imCokerSES : SES (im φ) G (coker φ) where
  inc := { app := fun U => (LinearMap.range (φ.app U)).subtype, app_smul := fun _ _ _ => rfl, naturality := fun _ => rfl }
  proj := { app := fun U => (LinearMap.range (φ.app U)).mkQ, app_smul := fun _ _ _ => rfl, naturality := fun _ => rfl }
  injective _ := Subtype.val_injective
  surjective _ := Submodule.Quotient.mk_surjective _
  exact _ := (Submodule.range_subtype _).trans (Submodule.ker_mkQ _).symm

end KerImCoker


section AffHoms

variable (F : OModulePresheaf π)

def AffHom.zeroFrom : AffHom (zero π) F where
  app _ := 0
  app_smul _ _ _ := by simp
  naturality _ := by ext; simp

def AffHom.zeroTo : AffHom F (zero π) where
  app _ := 0
  app_smul _ _ _ := Subsingleton.elim _ _
  naturality _ := LinearMap.ext fun _ => Subsingleton.elim _ _

def AffSES.zeroLeft : AffSES (zero π) F F where
  inc := AffHom.zeroFrom F
  proj := AffHom.id F
  injective _ := fun _ _ _ => Subsingleton.elim _ _
  surjective _ := Function.surjective_id
  exact _ := by
    show LinearMap.range (0 : _ →ₗ[R] _) = LinearMap.ker LinearMap.id
    rw [LinearMap.range_zero, LinearMap.ker_id]

def AffHom.powOne : AffHom (F.pow 1) F where
  app U := LinearMap.proj (R := R) (φ := fun _ : Fin 1 => F.obj U.1) 0
  app_smul _ _ _ := rfl
  naturality _ := rfl

def AffSES.powOne : AffSES (F.pow 1) F (zero π) where
  inc := AffHom.powOne F
  proj := AffHom.zeroTo F
  injective _ := fun f g h => funext fun j => Fin.fin_one_eq_zero j ▸ h
  surjective _ := fun x => ⟨0, Subsingleton.elim _ _⟩
  exact U := by
    apply le_antisymm
    · exact fun x _ => LinearMap.mem_ker.mpr (Subsingleton.elim _ _)
    · exact fun x _ => ⟨fun _ => x, rfl⟩

end AffHoms


def HasDevissageStep : Prop :=
  ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsSeparated π]
    [IsNoetherian V] (F : OModulePresheaf π) (_ : F.IsCoherent) (_ : F.IsQuasicoherent) (Y : Closeds V)
    (_ : (Y : Set V).Nonempty) (_ : F.SupportedIn Y)
    (_ : ∀ U : V.affineOpens, ∀ a ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U, ∀ x : F.obj U.1, a • x = 0),
    Nonempty (F.DevissageStep Y)

end OModulePresheaf

end AlgebraicGeometry

end
