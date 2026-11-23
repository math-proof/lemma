module

public import Theorem.Scheme.TwoAffineOpenCover
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}


public theorem isScalarTower_sections (c : X ⟶ Spec (.of R)) (M : X.Modules) (U : X.Opens) :
    letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
    IsScalarTower R Γ(X, U) Γ(M, U) :=
  letI := algebraOfHom c U; letI := moduleSectionsOfHom c M U
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl


public theorem restrictSections_apply (c : X ⟶ Spec (.of R)) (M : X.Modules) {U V : X.Opens} (h : V ≤ U) (x : Γ(M, U)) :
    letI := moduleSectionsOfHom c M U; letI := moduleSectionsOfHom c M V
    restrictSections c M h x = M.presheaf.map (homOfLE h).op x := rfl

variable (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R)) (M : X.Modules)


public theorem sectionsOf_M0 : (𝒱.sectionsOf c M).M0 = Γ(M, 𝒱.U0) := rfl

public theorem sectionsOf_M1 : (𝒱.sectionsOf c M).M1 = Γ(M, 𝒱.U1) := rfl

public theorem sectionsOf_M01 : (𝒱.sectionsOf c M).M01 = Γ(M, 𝒱.U0 ⊓ 𝒱.U1) := rfl

public theorem sectionsOf_r0_apply (x : Γ(M, 𝒱.U0)) :
    (𝒱.sectionsOf c M).r0 (show (𝒱.sectionsOf c M).M0 from x)
      = M.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op x := rfl

public theorem sectionsOf_r1_apply (x : Γ(M, 𝒱.U1)) :
    (𝒱.sectionsOf c M).r1 (show (𝒱.sectionsOf c M).M1 from x)
      = M.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op x := rfl

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
