import Mathlib
import Lemma.AlgebraicGeometry.TwoAffineOpenCover
import Lemma.AlgebraicGeometry.TwoChartCechLaurentChart

set_option autoImplicit false

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open CategoryTheory CategoryTheory.Limits Opposite

variable {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))


variable {𝒱 c}

def sectionAlgHom (σ : Spec (.of R) ⟶ X) (hσ : σ ≫ c = 𝟙 _) (hU : Set.range σ.base ⊆ (𝒱.U0 : Set X)) :
    (𝒱.cover c).A0 →ₐ[R] R :=
  letI := algebraOfHom c 𝒱.U0
  { (σ.appLE 𝒱.U0 ⊤ (fun x _ => hU ⟨x, rfl⟩) ≫ (Scheme.ΓSpecIso (.of R)).hom).hom with
    commutes' := fun r => by
      change ((Scheme.ΓSpecIso (.of R)).inv ≫ (c.appLE ⊤ 𝒱.U0 le_top ≫ σ.appLE 𝒱.U0 ⊤ _) ≫
        (Scheme.ΓSpecIso (.of R)).hom).hom r = r
      rw [Scheme.Hom.appLE_comp_appLE]
      suffices key : ∀ (φ : Spec (.of R) ⟶ Spec (.of R)), φ = 𝟙 _ → ∀ (e : (⊤ : (Spec (.of R)).Opens) ≤ φ ⁻¹ᵁ ⊤),
          (Scheme.ΓSpecIso (.of R)).inv ≫ φ.appLE ⊤ ⊤ e ≫ (Scheme.ΓSpecIso (.of R)).hom = 𝟙 _ by
        rw [key _ hσ]; rfl
      rintro φ rfl e
      have hid : (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).appLE ⊤ ⊤ e = 𝟙 _ := by
        change (𝟙 (Spec (.of R)) : Spec (.of R) ⟶ Spec (.of R)).app ⊤ ≫ (Spec (.of R)).presheaf.map _ = _
        rw [Scheme.Hom.id_app]
        erw [Category.id_comp]
        exact (congrArg (Spec (.of R)).presheaf.map (Subsingleton.elim _ _)).trans ((Spec (.of R)).presheaf.map_id _)
      rw [hid, Category.id_comp, Iso.inv_hom_id] }

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
