import Mathlib
import Lemma.MvFormalGroup.NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Def.CerednikDrinfeld_DrinfeldQuadruple
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Lemma.CerednikDrinfeld.GradedCartierNModule
import Lemma.CerednikDrinfeld.CartierModuleModel
import Abbrev.CerednikDrinfeld_CartierQuadruple
import Def.CerednikDrinfeld_CartierQuadrupleVia

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]


theorem isCartierQuadruple_iff_exists_via (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B) :
    t.IsCartierQuadruple ι hcΦ rΦ ψ Q ↔
      IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧
      ∃ (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
        (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))), t.IsCartierQuadrupleVia ι hcΦ rΦ ψ Q τ₀ τ₁ := by
  constructor
  · rintro ⟨hOD, τ₀, τ₁, h⟩; exact ⟨hOD, τ₀, τ₁, hOD, h⟩
  · rintro ⟨hOD, τ₀, τ₁, -, h⟩; exact ⟨hOD, τ₀, τ₁, h⟩

end CerednikDrinfeld.SpecialFormal.Rigidified
