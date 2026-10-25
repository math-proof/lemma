import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Def.CerednikDrinfeld_DrinfeldQuadruple
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Instance.CerednikDrinfeld_GradedCartierNModule
import Lemma.CerednikDrinfeld.CartierModuleModel
import Abbrev.CerednikDrinfeld_CartierQuadruple

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

open CerednikDrinfeld.FormalODModule MvFormalGroup MvFormalGroup.CartierModule

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

def IsCartierQuadrupleVia (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B)
    (τ₀ : Q.T₀ ≃ₗ[B] ↥(t.X.lieZero (structureMap ι ψ)))
    (τ₁ : Q.T₁ ≃ₗ[B] ↥(t.X.lieOne (structureMap ι ψ))) : Prop :=
  IsODHom (t.Φbar ψ) t.Xbar t.ρ ∧

    (∀ s : Q.T₀, ((τ₁ (Q.Pi₀ s) : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₀ s : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie)) ∧
    (∀ s : Q.T₁, ((τ₀ (Q.Pi₁ s) : ↥(t.X.lieZero (structureMap ι ψ))) : t.X.Lie) =
        t.X.lieVarpi ((τ₁ s : ↥(t.X.lieOne (structureMap ι ψ))) : t.X.Lie)) ∧

    ∀ (hOD : IsODHom (t.Φbar ψ) t.Xbar t.ρ) (x : PrimeSpectrum B),

      (∀ v, v ∈ Q.N₀ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v) ∧

      (∀ v, v ∈ Q.N₁ x ↔
        ∃ (f : B) (_ : f ∉ x.asIdeal) (hc : t.IsGradedS ι ψ (awayHom f))
          (hcb : t.IsGradedSbar ι ψ (awayHom f)) (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L),
          ∃ z, t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₀ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 0 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₀)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₀ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₀ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₀ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i)) ∧

      (∀ (v : Fin 2 → ℚ_[p]) (hv : v ∈ Q.N₁ x) (f : B) (hf : f ∉ x.asIdeal)
          (hc : t.IsGradedS ι ψ (awayHom f)) (hcb : t.IsGradedSbar ι ψ (awayHom f))
          (hcΦf : IsGradedPhiS (Φ := Φ) ι ψ (awayHom f))
          (L : _) (hL : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).IsCanonicalLMap L)
          (z : _) (hz : t.IsEtaSection ι hcΦ rΦ ψ hOD (awayHom f) hc hcb hcΦf L hL 1 z v),
        ∃ (m : ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).M) (s : Q.T₁)
          (b : x.asIdeal.primeCompl),
          ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).vRange.mkQ m =
            ((t.XS (awayHom f)).toGradedCartierModuleData _ hc).u L
              hL.isCartierLMap.map_verschiebung ⟨z, (AddSubgroup.mem_inf.mp hz.1).1⟩ ∧
          Q.u₁ x ((1 : Bloc x) ⊗ₜ[ℤ_[p]] (⟨v, hv⟩ : ↥(Q.N₁ x))) = LocalizedModule.mk s b ∧
          ∀ i, locHom x ((τ₁ s : t.X.Lie) i) =
            locHom x (b : B) * awayToLoc x f hf (tangent m i))

end CerednikDrinfeld.SpecialFormal.Rigidified
