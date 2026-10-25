import Lemma.PrimeNormIndex.AdmissibleExpAt
import Def.NormIndex_AdmissibleExpOfDegree

set_option autoImplicit false

noncomputable section

open IsDedekindDomain
open LanglandsTunnell.P2.Artin

namespace NumberField.NormIndex

variable (K L : Type*) [Field K] [NumberField K] [Field L] [Algebra K L]


theorem IsAdmissibleModulusOfDegree.of_dvd {n : ℕ} {𝔣 𝔣' : Ideal (𝓞 K)}
    (h : IsAdmissibleModulusOfDegree K L n 𝔣) (hd : 𝔣 ∣ 𝔣') (h0 : 𝔣' ≠ ⊥) :
    IsAdmissibleModulusOfDegree K L n 𝔣' :=
  ⟨h0, fun v hv => (h.2 v hv).trans hd⟩

omit [NumberField K] in

theorem admissibleExpOfDegree_finrank (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K (Module.finrank K L) v =
      (1 + ∑ p ∈ (Module.finrank K L).primeFactors,
        ((Module.finrank K L).factorization p + 1) *
          Ideal.ramificationIdx' (Ideal.span {(p : ℤ)}) v.asIdeal : ℕ) :=
  rfl

omit [NumberField K] in

theorem admissibleExpOfDegree_eq_admissibleExpAt {ℓ : ℕ} (hℓ : ℓ.Prime)
    (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K ℓ v = PrimeNormIndex.admissibleExpAt K ℓ v := by
  unfold admissibleExpOfDegree PrimeNormIndex.admissibleExpAt
  rw [hℓ.primeFactors, Finset.sum_singleton, hℓ.factorization_self]
  omega

omit [NumberField K] in

theorem admissibleExpOfDegree_twentyFour (v : HeightOneSpectrum (𝓞 K)) :
    admissibleExpOfDegree K 24 v = admissibleExp K v := by
  unfold admissibleExpOfDegree admissibleExp
  have h24 : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
  have hpf : (24 : ℕ).primeFactors = {2, 3} := by
    rw [h24, Nat.primeFactors_mul (by norm_num) (by norm_num),
      Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two, Nat.prime_three.primeFactors]
    rfl
  have hf2 : (24 : ℕ).factorization 2 = 3 := by
    rw [h24, Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_two.factorization_pow,
      Nat.prime_three.factorization]
    simp
  have hf3 : (24 : ℕ).factorization 3 = 1 := by
    rw [h24, Nat.factorization_mul (by norm_num) (by norm_num), Nat.prime_two.factorization_pow,
      Nat.prime_three.factorization]
    simp
  rw [hpf, Finset.sum_pair (by norm_num : (2 : ℕ) ≠ 3), hf2, hf3]
  push_cast
  omega

theorem isAdmissibleModulusOfDegree_iff_at {ℓ : ℕ} (hℓ : ℓ.Prime) (𝔣 : Ideal (𝓞 K)) :
    IsAdmissibleModulusOfDegree K L ℓ 𝔣 ↔ PrimeNormIndex.IsAdmissibleModulusAt K L ℓ 𝔣 := by
  unfold IsAdmissibleModulusOfDegree PrimeNormIndex.IsAdmissibleModulusAt
  simp only [admissibleExpOfDegree_eq_admissibleExpAt K hℓ]

theorem isAdmissibleModulusOfDegree_twentyFour_iff (𝔣 : Ideal (𝓞 K)) :
    IsAdmissibleModulusOfDegree K L 24 𝔣 ↔ IsAdmissibleModulus K L 𝔣 := by
  unfold IsAdmissibleModulusOfDegree IsAdmissibleModulus
  simp only [admissibleExpOfDegree_twentyFour K]

end NumberField.NormIndex

end
