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

namespace CerednikDrinfeld.SpecialFormal.ModuliPackage

def IsPeriodMap
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
  (∀ (B : Type) [CommRing B] [IsNoetherianRing B] [Algebra ℤ_[p] B] (ψ : WittVector p k →+* B)
      (hB : IsNilpotent (p : B)) (t : Rigidified p Φ B), t.IsAdmissible ι ψ →
      ∀ Q : DrinfeldDatum (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsCartierQuadruple ι hcΦ rΦ ψ Q →
        Q.IsQuadrupleOf (θ B ψ hB (η B ψ hB t))) ∧
  (∀ (B B' : Type) [CommRing B] [CommRing B'] [IsNoetherianRing B] [IsNoetherianRing B'] [Algebra ℤ_[p] B] [Algebra ℤ_[p] B']
    (ψ : WittVector p k →+* B) (ψ' : WittVector p k →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (f : B →ₐ[ℤ_[p]] B')
    (hf : (f : B →+* B').comp ψ = ψ') (x : M.obj B ψ hB),
    DeligneDatum.IsBaseChange (K := ℚ_[p]) (π := (p : ℤ_[p])) f (θ B ψ hB x)
      (θ B' ψ' hB' (M.map hB hB' (f : B →+* B') hf x)))

end CerednikDrinfeld.SpecialFormal.ModuliPackage
