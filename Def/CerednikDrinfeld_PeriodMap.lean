import Mathlib
import Instance.MvFormalGroup_NegV2
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Def.CerednikDrinfeld_DrinfeldQuadruple
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Instance.CerednikDrinfeld_GradedCartierNModule
import Lemma.CerednikDrinfeld.CartierModuleModel
import Abbrev.CerednikDrinfeld_CartierQuadruple
import Def.CerednikDrinfeld_PeriodMapSpec

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega

open scoped PadicInt Padic

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]

def IsPeriodValue (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=
  ∃ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q ∧ Q.IsQuadrupleOf d

noncomputable def periodValue (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d) :
    OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B :=
  h.choose

end CerednikDrinfeld.SpecialFormal.Rigidified

namespace CerednikDrinfeld.SpecialFormal.ModuliPackage

def IsPeriodMapOn
(p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [IsAlgClosed k]
(ι : Zp2 p →+* WittVector p k)
(Φ : FormalODModule p (WittVector p k ⧸ pIdeal p (WittVector p k)))
(M : ModuliPackage.{0, 0} p (WittVector p k))
(η : ∀ (B : Type) [CommRing B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
Rigidified p Φ B → M.obj B ψ hB)
(hcΦ : IsCompl (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 0) (Φ.gradedPiece ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) 1))
(rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData ((Ideal.Quotient.mk (pIdeal p (WittVector p k))).comp ι) hcΦ).NMod)
(θ : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B) (hB : IsNilpotent (p : B)),
M.obj B ψ hB → OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B) : Prop :=
  ∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
    (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
    t.IsPeriodValue ι hcΦ rΦ ψ (θ B ψ hB (η B ψ hB t))

end CerednikDrinfeld.SpecialFormal.ModuliPackage
