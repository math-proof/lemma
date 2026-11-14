import Mathlib
import Lemma.MvPowerSeries.NegV2
import Lemma.MvPowerSeries.SpecialFormalModule
import Def.CerednikDrinfeld_FormalUpperHalfPlaneDatum
import Def.CerednikDrinfeld_DrinfeldQuadruple
import Lemma.Fin.GradedCartierModuleData
import Lemma.Submodule.GradedCartierNModule
import Lemma.FormalGroup.CartierModuleModel
import Abbrev.CerednikDrinfeld_CartierQuadruple
import Def.CerednikDrinfeld_PeriodMapSpec
import Def.CerednikDrinfeld_PeriodMap

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalOmega FormalGroup Fin Submodule MvPowerSeries

open scoped PadicInt Padic

namespace CerednikDrinfeld.SpecialFormal.Rigidified

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]
variable {Φ : FormalODModule p (O ⧸ pIdeal p O)} {B : Type} [CommRing B]


theorem periodValue_spec (ι : Zp2 p →+* O)
    (hcΦ : IsCompl (Φ.gradedPiece (jbar ι) 0) (Φ.gradedPiece (jbar ι) 1))
    (rΦ : (Fin 2 → ℤ_[p]) →+ (Φ.toGradedCartierModuleData (jbar ι) hcΦ).NMod)
    [Algebra ℤ_[p] B] (ψ : O →+* B) (t : Rigidified p Φ B)
    (h : ∃ d : OmegaObj (K := ℚ_[p]) (p : ℤ_[p]) B, t.IsPeriodValue ι hcΦ rΦ ψ d) :
    t.IsPeriodValue ι hcΦ rΦ ψ (t.periodValue ι hcΦ rΦ ψ h) :=
  h.choose_spec

end CerednikDrinfeld.SpecialFormal.Rigidified
