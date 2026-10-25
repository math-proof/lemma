import Mathlib
import Abbrev.ModularCurve_XHDRModelAtP
import Abbrev.ModularCurve_DRModelPackageCrossingFrame
import Abbrev.ModularCurve_XHDRModelAtPCrossingFrame

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace XHDRLevel

variable {p : ℕ} (Γ : Subgroup SL(2, ℤ)) (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))


def bcMap {O : Type} [CommRing O] (ρO : R p →+* O) {κ : Type} [CommRing κ] (toκ : O →+* κ)
    {toκ' : R p →+* κ} (h : toκ.comp ρO = toκ') :
    fibre (Γ := Γ) (hj := hj) toκ' ⟶ XO Γ hj ρO :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp, h])

end XHDRLevel

end ModularCurve

end
