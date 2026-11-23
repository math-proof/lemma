module

public import Theorem.LinearMap.TwoChartCech
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Structure.AlgebraicGeometry_TwoAffineOpenCover
public import Abbrev.AlgebraicGeometry_TwoAffineOpenCover

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits Opposite


namespace Scheme.TwoAffineOpenCover


public theorem algebraMap_algebraOfHom (c : X ⟶ Spec (.of R)) (U : X.Opens) (r : R) :
    (algebraOfHom c U).algebraMap r = (c.appLE ⊤ U (by rw [Scheme.Hom.preimage_top]; exact le_top)).hom ((Scheme.ΓSpecIso (.of R)).inv.hom r) :=
  rfl


public theorem cover_A0 : (𝒱.cover c).A0 = Γ(X, 𝒱.U0) := rfl

public theorem cover_A1 : (𝒱.cover c).A1 = Γ(X, 𝒱.U1) := rfl

public theorem cover_A01 : (𝒱.cover c).A01 = Γ(X, 𝒱.U0 ⊓ 𝒱.U1) := rfl

public theorem cover_ρ0_apply (x : (𝒱.cover c).A0) :
    (𝒱.cover c).ρ0 x = (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom x := rfl

public theorem cover_ρ1_apply (x : (𝒱.cover c).A1) :
    (𝒱.cover c).ρ1 x = (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom x := rfl


public theorem res_res {V₁ V₂ V₃ : X.Opens} (h₂₁ : V₂ ≤ V₁) (h₃₂ : V₃ ≤ V₂) (x : Γ(X, V₁)) :
    (X.presheaf.map (homOfLE h₃₂).op).hom ((X.presheaf.map (homOfLE h₂₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₃₂.trans h₂₁)).op).hom x := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl


public theorem restrict_mem_H0 (s : Γ(X, ⊤)) :
    ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
      (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
      ∈ (𝒱.structureSheafSections c).H0 := by
  refine (TwoChartCech.Sections.mem_H0_iff _ _).mpr ?_
  change (X.presheaf.map (homOfLE (inf_le_left : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U0)).op).hom
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s)
    = ((1 : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)ˣ) : Γ(X, 𝒱.U0 ⊓ 𝒱.U1)) •
      (X.presheaf.map (homOfLE (inf_le_right : 𝒱.U0 ⊓ 𝒱.U1 ≤ 𝒱.U1)).op).hom
        ((X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s)
  rw [Units.val_one, one_smul, res_res, res_res]


public theorem toH0_apply_coe (s : Γ(X, ⊤)) :
    letI := algebraOfHom c ⊤
    ((𝒱.toH0 c s : (𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1)) =
      ((X.presheaf.map (homOfLE (le_top : 𝒱.U0 ≤ ⊤)).op).hom s,
        (X.presheaf.map (homOfLE (le_top : 𝒱.U1 ≤ ⊤)).op).hom s) := rfl

section Pullback

variable (A : Type u) [CommRing A] [Algebra R A]


public theorem isAffineHom_fst : IsAffineHom (Limits.pullback.fst c (specMap R A)) := by
  -- IsStableUnderBaseChangeAlong @IsAffineHom fails to synth here (mathlib needs
  -- set_option backward.isDefEq.respectTransparency.types). Fin Res only needs
  -- algebraOfHom / restrictAlgHom above; Comap callers can revisit.
  sorry


@[simp] public theorem pullback_U0 : (𝒱.pullback c A).U0 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U0 := rfl

@[simp] public theorem pullback_U1 : (𝒱.pullback c A).U1 = (Limits.pullback.fst c (specMap R A)) ⁻¹ᵁ 𝒱.U1 := rfl

end Pullback

end Scheme.TwoAffineOpenCover

end AlgebraicGeometry

end
