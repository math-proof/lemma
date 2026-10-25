import Def.PrimeNormIndex_AdmissibleExpAt

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open LanglandsTunnell.P2.Artin

namespace NumberField.NormIndex

variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]

def admissibleExpOfDegree (n : ℕ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  1 + ∑ p ∈ n.primeFactors,
    (n.factorization p + 1) * Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal

def IsAdmissibleModulusOfDegree (n : ℕ) (𝔣 : Ideal (𝓞 K)) : Prop :=
  𝔣 ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K),
    (primeAbove K L v).inertia (L ≃ₐ[K] L) ≠ ⊥ → v.asIdeal ^ admissibleExpOfDegree K n v ∣ 𝔣

end NumberField.NormIndex

end
