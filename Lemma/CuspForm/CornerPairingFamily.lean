import Lemma.CohCarrier.Inst
import Lemma.ModularCurve.PeriodMap
import Lemma.CohCarrier.LevelPairing
import Def.CuspForm_CornerPairingFamily

set_option autoImplicit false

set_option linter.unusedVariables false

noncomputable section

namespace CuspForm

open CohCarrier IharaLemma IharaTower


namespace Bfam

section Corner

variable (𝒪 : Type) [CommRing 𝒪] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ H 1)
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M H 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M H 𝒪)]


@[simp] theorem cornerInclusion_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x : cd.cornerModule) :
    cornerInclusion 𝒪 M H h₁ cd hW x = ⟨x, hW _ x.2⟩ := rfl


@[simp] theorem cornerRestrict_apply (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁))
    (x y : cd.cornerModule) :
    cornerRestrict 𝒪 M H h₁ cd hW x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := rfl

theorem pairing_eq_cornerRestrict_iff (cd : H1CornerData (𝒪 := 𝒪) M H 𝒪 𝕋)
    (hW : ∀ v : H1 M H 𝒪, v ∈ cornerSubmodule (M := H1 M H 𝒪) (cd.split.e cd.idx) →
      v ∈ (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ H 1 𝒪 𝒪 h₁)) :
    cd.pairing.B = cornerRestrict 𝒪 M H h₁ cd hW ↔
      ∀ x y : cd.cornerModule, cd.pairing.B x y = Bfam 𝒪 M H h₁ ⟨x, hW _ x.2⟩ ⟨y, hW _ y.2⟩ := by
  constructor
  · intro h x y
    rw [h]
    rfl
  · intro h
    exact LinearMap.ext₂ fun x y => h x y

end Corner

end Bfam

end CuspForm

end
