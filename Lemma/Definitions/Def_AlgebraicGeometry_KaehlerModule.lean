import Mathlib
import Lemma.Definitions.Def_PresheafOfModules_ExteriorPower
import Lemma.Definitions.Def_AlgebraicGeometry_ModulesDet

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

abbrev topPresheaf (d : ℕ) : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj f.kaehlerPresheaf

@[simp] lemma kaehlerPresheaf_obj (U : (X.Opens)ᵒᵖ) :
    f.kaehlerPresheaf.obj U = CommRingCat.KaehlerDifferential (f.constToPresheaf.app U) := rfl

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

theorem kaehlerToSections_add (U : X.Opens) (s t : f.kaehlerPresheaf.obj (op U)) :
    f.kaehlerToSections U (s + t) = f.kaehlerToSections U s + f.kaehlerToSections U t :=
  map_add (f.kaehlerToSectionsₗ U) s t

theorem kaehlerPresheaf_nontrivial_polynomial (A : Type u) [CommRing A] [Nontrivial A] :
    letI f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
      Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    Nontrivial (f.kaehlerPresheaf.obj (op ⊤)) := by
  set f : Spec (CommRingCat.of (Polynomial A)) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A (Polynomial A))) with hf

  let Γ' : Type u := Γ(Spec (CommRingCat.of (Polynomial A)), ⊤)
  letI algA : Algebra A Γ' := f.sectionsAlgebra ⊤
  let e : Γ' ≃+* Polynomial A := (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).commRingCatIsoToRingEquiv
  letI : Algebra Γ' (Polynomial A) := e.toRingHom.toAlgebra

  have hcomp : (algebraMap Γ' (Polynomial A)).comp (algebraMap A Γ') = algebraMap A (Polynomial A) := by
    refine RingHom.ext fun a => ?_
    change (Scheme.ΓSpecIso (CommRingCat.of (Polynomial A))).hom.hom
      ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = algebraMap A (Polynomial A) a
    have h1 : f.appLE ⊤ ⊤ le_top = f.appTop := by
      simp [Scheme.Hom.appLE, Scheme.Hom.appTop]
    rw [h1]
    have h2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap A (Polynomial A)))
    rw [← hf] at h2
    have h3 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) h2
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at h3
    rw [h3]
    change algebraMap A (Polynomial A) (((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).hom a) = _
    rw [Iso.inv_hom_id]; rfl
  haveI : IsScalarTower A Γ' (Polynomial A) := IsScalarTower.of_algebraMap_eq' hcomp.symm
  have hsurj : Function.Surjective (KaehlerDifferential.map A A Γ' (Polynomial A)) :=
    KaehlerDifferential.map_surjective_of_surjective A A (h := e.surjective)
  haveI : Nontrivial (Ω[Polynomial A⁄A]) :=
    (KaehlerDifferential.polynomialEquiv A).toEquiv.nontrivial
  exact hsurj.nontrivial

end AlgebraicGeometry.Scheme.Hom

end

/-- info: 'AlgebraicGeometry.Scheme.Hom.kaehlerToSections_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AlgebraicGeometry.Scheme.Hom.kaehlerToSections_add

/--
info: 'AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf_nontrivial_polynomial
