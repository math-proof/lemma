import Lemma.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Modules.Sheaf

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

@[reducible] def moduleSectionsOfHom (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    Module R Γ(M, U) :=
  letI := algebraOfHom c U
  Module.compHom Γ(M, U) (algebraMap R Γ(X, U))

theorem isScalarTower_sections (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
    IsScalarTower R Γ(X, U) Γ(M, U) :=
  letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

def restrictSections (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    Γ(M, U) →ₗ[R] Γ(M, V) :=
  letI := algebraOfHom c U; letI := algebraOfHom c V
  letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
  { toFun := fun x => M.presheaf.map (homOfLE h).op x
    map_add' := fun x y => map_add _ x y
    map_smul' := fun r x => by
      show M.presheaf.map (homOfLE h).op ((algebraMap R Γ(X, U) r) • x)
        = (algebraMap R Γ(X, V) r) • M.presheaf.map (homOfLE h).op x
      rw [Scheme.Modules.map_smul]
      congr 1
      exact (restrictAlgHom c h).commutes r }

theorem restrictSections_apply (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    restrictSections c M h x = M.presheaf.map (homOfLE h).op x := rfl

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules)

def sectionsOf : TwoChartCech.Sections (𝒱.cover c) :=
  letI : Module (𝒱.cover c).A0 Γ(M, 𝒱.U0) := inferInstanceAs (Module Γ(X, 𝒱.U0) Γ(M, 𝒱.U0))
  letI : Module (𝒱.cover c).A1 Γ(M, 𝒱.U1) := inferInstanceAs (Module Γ(X, 𝒱.U1) Γ(M, 𝒱.U1))
  letI : Module (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) :=
    inferInstanceAs (Module Γ(X, 𝒱.U0 ⊓ 𝒱.U1) Γ(M, 𝒱.U0 ⊓ 𝒱.U1))
  letI : Module R Γ(M, 𝒱.U0) := moduleSectionsOfHom c M 𝒱.U0
  letI : Module R Γ(M, 𝒱.U1) := moduleSectionsOfHom c M 𝒱.U1
  letI : Module R Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := moduleSectionsOfHom c M (𝒱.U0 ⊓ 𝒱.U1)
  haveI : IsScalarTower R (𝒱.cover c).A0 Γ(M, 𝒱.U0) := isScalarTower_sections c M 𝒱.U0
  haveI : IsScalarTower R (𝒱.cover c).A1 Γ(M, 𝒱.U1) := isScalarTower_sections c M 𝒱.U1
  haveI : IsScalarTower R (𝒱.cover c).A01 Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := isScalarTower_sections c M (𝒱.U0 ⊓ 𝒱.U1)
  { M0 := Γ(M, 𝒱.U0)
    M1 := Γ(M, 𝒱.U1)
    M01 := Γ(M, 𝒱.U0 ⊓ 𝒱.U1)
    r0 := restrictSections c M inf_le_left
    r1 := restrictSections c M inf_le_right
    r0_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)) a m
    r1_smul := fun a m => by
      exact Scheme.Modules.map_smul M (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)) a m }

theorem sectionsOf_M0 : (𝒱.sectionsOf c M).M0 = Γ(M, 𝒱.U0) := rfl
theorem sectionsOf_M1 : (𝒱.sectionsOf c M).M1 = Γ(M, 𝒱.U1) := rfl
theorem sectionsOf_M01 : (𝒱.sectionsOf c M).M01 = Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := rfl
theorem sectionsOf_r0_apply (x : Γ(M, 𝒱.U0)) :
    (𝒱.sectionsOf c M).r0 (show (𝒱.sectionsOf c M).M0 from x)
      = M.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op x := rfl
theorem sectionsOf_r1_apply (x : Γ(M, 𝒱.U1)) :
    (𝒱.sectionsOf c M).r1 (show (𝒱.sectionsOf c M).M1 from x)
      = M.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op x := rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
