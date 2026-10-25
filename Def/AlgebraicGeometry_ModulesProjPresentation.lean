import Mathlib
import Lemma.AlgebraicGeometry.ProjSpace
import Structure.AlgebraicGeometry_ModulesProjPresentation

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite MvPolynomial HomogeneousLocalization

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Scheme.Modules

variable {R : Type u} [CommRing R] {X : Scheme.{u}}


def FiniteBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsFinite 𝔓.toProj

def ClosedImmersionBySections (M : X.Modules) (f : X ⟶ Spec (.of R)) : Prop :=
  ∃ (N : ℕ) (𝔓 : M.ProjPresentation f N), IsClosedImmersion 𝔓.toProj

end Scheme.Modules

namespace ProjSpace

variable (R : Type u) [CommRing R]

def awayZeroEval :
    HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R) →+* R :=
  (IsLocalization.Away.lift (S := Localization.Away (X 0 : MvPolynomial (Fin 1) R))
      (X 0 : MvPolynomial (Fin 1) R)
      (g := (MvPolynomial.aeval (R := R) (fun _ : Fin 1 => (1 : R))).toRingHom)
      (by simp)).comp
    (algebraMap (HomogeneousLocalization.Away (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0 : MvPolynomial (Fin 1) R))
      (Localization.Away (X 0 : MvPolynomial (Fin 1) R)))

def pointOfProjZero : Spec (.of R) ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin 1) R) :=
  Spec.map (CommRingCat.ofHom (awayZeroEval R)) ≫
    Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos

theorem pointOfProjZero_π : pointOfProjZero R ≫ π R 0 = 𝟙 _ := by
  rw [pointOfProjZero, Category.assoc, awayι_comp_π, ← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext r : 2
  change awayZeroEval R (algebraMap R _ r) = r
  simp only [awayZeroEval, RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.algebraMap_apply, val_algebraMap, IsLocalization.Away.lift_eq]
  simp

theorem pointOfProjZero_preimage_basicOpen :
    pointOfProjZero R ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
  rw [pointOfProjZero, Scheme.Hom.comp_preimage]
  have : Proj.awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos ⁻¹ᵁ
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) = ⊤ := by
    rw [← Proj.opensRange_awayι (MvPolynomial.homogeneousSubmodule (Fin 1) R) (X 0) (X_mem_one R 0 0) one_pos]
    exact Scheme.Hom.preimage_opensRange _
  rw [this]
  rfl

end ProjSpace

variable (R : Type u) [CommRing R]

def Scheme.Modules.unitOne (X : Scheme.{u}) :
    Γ((SheafOfModules.unit X.ringCatSheaf : X.Modules), (⊤ : X.Opens)) :=
  (show Γ(X, ⊤) from 1)

def Scheme.Modules.ProjPresentation.unitSpec :
    Scheme.Modules.ProjPresentation (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)
      (𝟙 (Spec (.of R))) 0 where
  σ := fun _ => Scheme.Modules.unitOne (Spec (.of R))
  toProj := ProjSpace.pointOfProjZero R
  toProj_π := ProjSpace.pointOfProjZero_π R
  frame := fun i V _ => by
    have h : (Scheme.Modules.presheaf (SheafOfModules.unit (Spec (.of R)).ringCatSheaf : (Spec (.of R)).Modules)).map
        (homOfLE (le_top : V ≤ ⊤)).op (Scheme.Modules.unitOne (Spec (.of R)))
        = (show Γ(Spec (.of R), V) from 1) := by
      change ((Spec (.of R)).ringCatSheaf.obj.map (homOfLE (le_top : V ≤ ⊤)).op).hom 1 = 1
      exact map_one _
    rw [h]
    change Function.Bijective fun g : Γ(Spec (.of R), V) => g * 1
    simp only [mul_one]
    exact Function.bijective_id
  app_ratio_smul := fun i j => by
    have hi : i = 0 := Fin.eq_zero i
    have hj : j = 0 := Fin.eq_zero j
    subst hi hj
    rw [ProjSpace.ratio_self, map_one, map_one, one_smul]

end AlgebraicGeometry

end
