import Lemma.Definitions.Def_LanglandsTunnell_ArtinCoreCTM

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

omit [NumberField K] in

theorem admissibleExpAt_two_le (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpAt K 2 v ≤ admissibleExp K v := by
  unfold admissibleExpAt admissibleExp
  rw [show ((2 : ℕ) : ℤ) = (2 : ℤ) by norm_num]
  omega

omit [NumberField K] in

theorem admissibleExpAt_three_le (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpAt K 3 v ≤ admissibleExp K v := by
  unfold admissibleExpAt admissibleExp
  rw [show ((3 : ℕ) : ℤ) = (3 : ℤ) by norm_num]
  omega

theorem isAdmissibleModulusAt_two {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) :
    IsAdmissibleModulusAt K L 2 𝔣 :=
  ⟨h.1, fun v hv => dvd_trans (pow_dvd_pow _ (admissibleExpAt_two_le K v)) (h.2 v hv)⟩

theorem isAdmissibleModulusAt_three {𝔣 : Ideal (𝓞 K)} (h : IsAdmissibleModulus K L 𝔣) :
    IsAdmissibleModulusAt K L 3 𝔣 :=
  ⟨h.1, fun v hv => dvd_trans (pow_dvd_pow _ (admissibleExpAt_three_le K v)) (h.2 v hv)⟩

theorem IsAdmissibleModulusAt.of_dvd {ℓ : ℕ} {𝔣 𝔣' : Ideal (𝓞 K)}
    (h : IsAdmissibleModulusAt K L ℓ 𝔣) (hd : 𝔣 ∣ 𝔣') (h0 : 𝔣' ≠ ⊥) :
    IsAdmissibleModulusAt K L ℓ 𝔣' :=
  ⟨h0, fun v hv => (h.2 v hv).trans hd⟩

end NumberField.PrimeNormIndex

end
