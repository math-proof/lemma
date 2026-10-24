import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Ring
import Lemma.Definitions.Def_LanglandsTunnell_HonestLDatum

noncomputable section

open Polynomial IsDedekindDomain NumberField

namespace LanglandsTunnell.RankinSelberg

section Induced

variable (F : Type*) [Field F] {K : Type*} [Field K] [Algebra (𝓞 F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]

variable (K) in

def primeFibre (p : HeightOneSpectrum (𝓞 F)) : Set (HeightOneSpectrum (𝓞 K)) :=
  {𝔓 | 𝔓.under (𝓞 F) = p}

@[simp] theorem mem_primeFibre (p : HeightOneSpectrum (𝓞 F)) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ primeFibre F K p ↔ 𝔓.under (𝓞 F) = p :=
  Iff.rfl

def inducedFactor (c : HeightOneSpectrum (𝓞 K) → R) (𝔓 : HeightOneSpectrum (𝓞 K)) : R[X] :=
  C 1 - C (c 𝔓) * X ^ ((𝔓.under (𝓞 F)).asIdeal.inertiaDeg' 𝔓.asIdeal)

def inducedEulerPoly (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 F)) : R[X] :=
  ∏ᶠ 𝔓 ∈ primeFibre F K p, inducedFactor F c 𝔓

def inducedE1 (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 F)) : R :=
  -(inducedEulerPoly F c p).coeff 1

def inducedE2 (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 F)) : R :=
  (inducedEulerPoly F c p).coeff 2

def inducedE3 (c : HeightOneSpectrum (𝓞 K) → R) (p : HeightOneSpectrum (𝓞 F)) : R :=
  -(inducedEulerPoly F c p).coeff 3

end Induced

section RankinSelberg

variable {R : Type*} [CommRing R]

def rsEulerPoly (a b e₁ e₂ e₃ : R) : R[X] :=
  C 1
    + C (-(a * e₁)) * X
    + C (a ^ 2 * e₂ + b * e₁ ^ 2 - 2 * b * e₂) * X ^ 2
    + C (-(a ^ 3 * e₃) - a * b * e₁ * e₂ + 3 * a * b * e₃) * X ^ 3
    + C (a ^ 2 * b * e₁ * e₃ - 2 * b ^ 2 * e₁ * e₃ + b ^ 2 * e₂ ^ 2) * X ^ 4
    + C (-(a * b ^ 2 * e₂ * e₃)) * X ^ 5
    + C (b ^ 3 * e₃ ^ 2) * X ^ 6

private theorem rsEulerPoly_eq_prod (α₁ α₂ β₁ β₂ β₃ : R) :
    rsEulerPoly (α₁ + α₂) (α₁ * α₂) (β₁ + β₂ + β₃) (β₁ * β₂ + β₁ * β₃ + β₂ * β₃)
        (β₁ * β₂ * β₃) =
      (C 1 - C (α₁ * β₁) * X) * (C 1 - C (α₁ * β₂) * X) * (C 1 - C (α₁ * β₃) * X) *
        ((C 1 - C (α₂ * β₁) * X) * (C 1 - C (α₂ * β₂) * X) * (C 1 - C (α₂ * β₃) * X)) := by
  simp only [rsEulerPoly, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]
  ring

end RankinSelberg

section Datum

variable (F : Type*) [Field F] [NumberField F] {K : Type*} [Field K] [Algebra (𝓞 F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 F) (𝓞 K)]

def rsDatum (S : Finset (HeightOneSpectrum (𝓞 F))) (a b : HeightOneSpectrum (𝓞 F) → ℂ)
    (c : HeightOneSpectrum (𝓞 K) → ℂ) (gammaR gammaC gammaRDual gammaCDual : Multiset ℂ) :
    LDatum {p : HeightOneSpectrum (𝓞 F) // p ∉ S} where
  norm := fun p => Ideal.absNorm p.1.asIdeal
  euler := fun p =>
    rsEulerPoly (a p.1) (b p.1) (inducedE1 F c p.1) (inducedE2 F c p.1) (inducedE3 F c p.1)
  dual := fun p =>
    rsEulerPoly (a p.1 / b p.1) (b p.1)⁻¹ (inducedE1 F (fun 𝔓 => (c 𝔓)⁻¹) p.1)
      (inducedE2 F (fun 𝔓 => (c 𝔓)⁻¹) p.1) (inducedE3 F (fun 𝔓 => (c 𝔓)⁻¹) p.1)
  gammaR := gammaR
  gammaC := gammaC
  gammaRDual := gammaRDual
  gammaCDual := gammaCDual
  abscissa := 1
  center := 1 / 2
  degree := 6

end Datum

end LanglandsTunnell.RankinSelberg

end
