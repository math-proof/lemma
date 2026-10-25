import Mathlib
import Instance.PresheafOfModules_ExteriorPower
import Abbrev.AlgebraicGeometry_ModulesDet

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Hom

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

def constToPresheaf : (Functor.const (X.Opens)ᵒᵖ).obj (CommRingCat.of A) ⟶ X.presheaf where
  app U := (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appLE ⊤ U.unop le_top
  naturality U V i := by
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, Category.assoc]
    rw [Scheme.Hom.appLE_map]

@[reducible] def sectionsAlgebra (U : X.Opens) : Algebra A Γ(X, U) :=
  (f.constToPresheaf.app (op U)).hom.toAlgebra

def kaehlerPresheaf : X.PresheafOfModules :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' f.constToPresheaf

def kaehler : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj f.kaehlerPresheaf

def topDifferentials (d : ℕ) : X.Modules :=
  Scheme.Modules.det d f.kaehler


def kaehlerToSections (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U) : Type u) → (Γ(f.kaehler, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom s

def kaehlerToSectionsₗ (U : X.Opens) :
    (f.kaehlerPresheaf.obj (op U)) →ₗ[Γ(X, U)] (Γ(f.kaehler, U) : Type u) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    f.kaehlerPresheaf).app (op U)).hom

def topToSections (d : ℕ) (U : X.Opens) :
    (⋀[Γ(X, U)]^d (f.kaehlerPresheaf.obj (op U)) : Type u) → (Γ(f.topDifferentials d, U) : Type u) :=
  fun s => (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      ((Scheme.Modules.presheafExteriorPower X d).obj f.kaehler.val)).app (op U)).hom
    (exteriorPower.map d (f.kaehlerToSectionsₗ U) s)

end AlgebraicGeometry.Scheme.Hom

end
