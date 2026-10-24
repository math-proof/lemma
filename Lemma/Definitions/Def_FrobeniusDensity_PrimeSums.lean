import Lemma.Definitions.Def_FrobeniusDensity_BadPrimes
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.DedekindDomain.Factorization

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
  UniqueFactorizationMonoid
open scoped ENNReal NNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

noncomputable def normRpow (s : ℝ) (I : Ideal (𝓞 K)) : ℝ≥0∞ :=
  (Ideal.absNorm I : ℝ≥0∞) ^ (-s)

noncomputable def idealSum (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // I ≠ ⊥}, normRpow K s I.1

noncomputable def primeSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal

noncomputable def primeSqSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K), normRpow K s v.asIdeal ^ 2

variable {K}

def IsFactoredBy (T : Finset (HeightOneSpectrum (𝓞 K))) (I : Ideal (𝓞 K)) : Prop :=
  I ≠ ⊥ ∧ ∀ v : HeightOneSpectrum (𝓞 K), v.asIdeal ∣ I → v ∈ T

variable (K) in

noncomputable def factoredSum (T : Finset (HeightOneSpectrum (𝓞 K))) (s : ℝ) : ℝ≥0∞ :=
  ∑' I : {I : Ideal (𝓞 K) // IsFactoredBy T I}, normRpow K s I.1

lemma one_le_absNorm {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) : 1 ≤ Ideal.absNorm I :=
  Nat.one_le_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))

variable (K) in

noncomputable def primeFactors (I : Ideal (𝓞 K)) : Finset (HeightOneSpectrum (𝓞 K)) :=
  if hI : I = ⊥ then ∅ else (finite_setOf_dvd hI).toFinset

variable (K)

theorem exists_prime_liesOver (v : HeightOneSpectrum (𝓞 K)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.LiesOver (ratPrimeIdeal ℓ) := by
  have hJp : (v.asIdeal.under ℤ).IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hmem : (Ideal.absNorm v.asIdeal : ℤ) ∈ v.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap, algebraMap_int_eq, map_natCast]
    exact Ideal.absNorm_mem v.asIdeal
  have hJne : v.asIdeal.under ℤ ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot, Int.natCast_eq_zero] at hmem
    exact Nat.one_le_iff_ne_zero.mp (one_le_absNorm v.ne_bot) hmem
  refine ⟨(Submodule.IsPrincipal.generator (v.asIdeal.under ℤ)).natAbs,
    Int.prime_iff_natAbs_prime.mp
      (Submodule.IsPrincipal.prime_generator_of_isPrime _ hJne), ⟨?_⟩⟩
  rw [ratPrimeIdeal, Int.span_natAbs, Ideal.span_singleton_generator]

variable {K}

noncomputable def ratBelow (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (exists_prime_liesOver K v).choose

theorem ratBelow_prime (v : HeightOneSpectrum (𝓞 K)) : (ratBelow v).Prime :=
  (exists_prime_liesOver K v).choose_spec.1

instance liesOver_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.LiesOver (ratPrimeIdeal (ratBelow v)) :=
  (exists_prime_liesOver K v).choose_spec.2

variable (K)

noncomputable def degOneSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else (degOneCount K ℓ : ℝ≥0∞)) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def cutSum (S₀ : Finset ℕ) (s : ℝ) : ℝ≥0∞ :=
  ∑' ℓ : ℕ, (if ℓ ∈ S₀ then (degOneCount K ℓ : ℝ≥0∞) else 0) * (ℓ : ℝ≥0∞) ^ (-s)

noncomputable def tailSum (s : ℝ) : ℝ≥0∞ :=
  ∑' v : HeightOneSpectrum (𝓞 K),
    if (Ideal.absNorm v.asIdeal).Prime then 0 else normRpow K s v.asIdeal

noncomputable def tailConst : ℝ≥0∞ :=
  ∑' ℓ : ℕ, if ℓ.Prime then ((ℓ : ℝ≥0∞) ^ 2)⁻¹ else 0

noncomputable def idealCount (n : ℕ) : ℕ :=
  Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

noncomputable def zetaTerm (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else idealCount K n * (n : ℝ) ^ (-s)

end FrobeniusDensity
