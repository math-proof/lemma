import Instance.LanglandsTunnell_ArtinCoreCTM

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open LanglandsTunnell.P2.Artin

namespace NumberField.PrimeNormIndex

variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]

def admissibleExpAt (ℓ : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  2 * Ideal.ramificationIdx' (Ideal.span {(ℓ : ℤ)}) v.asIdeal + 1

def IsAdmissibleModulusAt (ℓ : ℕ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExpAt K ℓ v ∣ 𝔣

end NumberField.PrimeNormIndex

end
