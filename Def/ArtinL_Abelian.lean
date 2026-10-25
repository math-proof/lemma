import Mathlib
import Instance.LanglandsTunnell_ArtinFrobenius

set_option autoImplicit false

noncomputable section

open NumberField NumberField.InfinitePlace IsDedekindDomain
open scoped Classical

namespace ArtinL.Abelian

section Finite

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

variable (K M) in

def inertiaGroup (v : HeightOneSpectrum (𝓞 K)) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v).inertia (M ≃ₐ[K] M)

variable (K M) in

def ramificationGroup (v : HeightOneSpectrum (𝓞 K)) (i : ℕ) : Subgroup (M ≃ₐ[K] M) :=
  (LanglandsTunnell.P2.Artin.primeAbove K M v ^ (i + 1)).inertia (M ≃ₐ[K] M)

omit [NumberField M] [IsGalois K M] in

def IsUnramifiedAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : Prop :=
  ∀ σ ∈ inertiaGroup K M v, ψ σ = 1

def localValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℂ :=
  if IsUnramifiedAt ψ v then ((ψ (LanglandsTunnell.P2.Artin.artinFrob K M v) : ℂˣ) : ℂ) else 0

def idealValue (ψ : (M ≃ₐ[K] M) →* ℂˣ) (I : Ideal (𝓞 K)) : ℂ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K),
    localValue ψ v ^ (Associates.mk v.asIdeal).count (Associates.mk I).factors

def coeff (ψ : (M ≃ₐ[K] M) →* ℂˣ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else ∑ I ∈ (Ideal.finite_setOf_absNorm_eq (S := 𝓞 K) n).toFinset, idealValue ψ I

def LSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  _root_.LSeries (coeff ψ) s

def swanConductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card (ramificationGroup K M v (i + 1)) : ℚ) / (Nat.card (inertiaGroup K M v) : ℚ) *
      (if ∀ σ ∈ ramificationGroup K M v (i + 1), ψ σ = 1 then 0 else 1)

def conductorExponent (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : HeightOneSpectrum (𝓞 K)) : ℕ :=
  (if IsUnramifiedAt ψ v then 0 else 1) + ⌈swanConductor ψ v⌉₊

def conductor (ψ : (M ≃ₐ[K] M) →* ℂˣ) : Ideal (𝓞 K) :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 K), v.asIdeal ^ conductorExponent ψ v

end Finite

section Archimedean

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

def IsPlusAt (ψ : (M ≃ₐ[K] M) →* ℂˣ) (v : InfinitePlace K) : Prop :=
  ∀ w : InfinitePlace M, w.comap (algebraMap K M) = v →
    ∀ σ ∈ MulAction.stabilizer (M ≃ₐ[K] M) w, ψ σ = 1

def nPlus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  Nat.card {v : InfinitePlace K // v.IsReal ∧ IsPlusAt ψ v}

def nMinus (ψ : (M ≃ₐ[K] M) →* ℂˣ) : ℕ :=
  nrRealPlaces K - nPlus ψ

end Archimedean

section Completed

variable {K M : Type*} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [IsGalois K M]

def completedLSeries (ψ : (M ≃ₐ[K] M) →* ℂˣ) (s : ℂ) : ℂ :=
  ((|(discr K : ℝ)| * (Ideal.absNorm (conductor ψ) : ℝ) : ℝ) : ℂ) ^ (s / 2) *
    Complex.Gammaℝ s ^ nPlus ψ * Complex.Gammaℝ (s + 1) ^ nMinus ψ *
    Complex.Gammaℂ s ^ nrComplexPlaces K * LSeries ψ s

end Completed

section OfSubgroup

variable {k F : Type*} [Field k] [Field F] [Algebra k F] [FiniteDimensional k F]

def ofSubgroup (H : Subgroup (F ≃ₐ[k] F)) (χ : H →* ℂˣ) :
    (F ≃ₐ[IntermediateField.fixedField H] F) →* ℂˣ :=
  χ.comp
    ((MulEquiv.subgroupCongr (IntermediateField.fixingSubgroup_fixedField H)).toMonoidHom.comp
      (IntermediateField.fixingSubgroupEquiv (IntermediateField.fixedField H)).symm.toMonoidHom)

end OfSubgroup

end ArtinL.Abelian

end
