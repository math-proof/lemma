import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Tactic.Ring
import Lemma.LanglandsTunnell.HonestLDatum
import Def.LanglandsTunnell_RankinSelbergEuler

noncomputable section

open Polynomial IsDedekindDomain NumberField

namespace LanglandsTunnell.RankinSelberg

section Induced

variable (F : Type*) [Field F] {K : Type*} [Field K] [Algebra (𝓞 F) (𝓞 K)]
  [Algebra.IsIntegral (𝓞 F) (𝓞 K)] {R : Type*} [CommRing R]


@[simp] theorem mem_primeFibre (p : HeightOneSpectrum (𝓞 F)) (𝔓 : HeightOneSpectrum (𝓞 K)) :
    𝔓 ∈ primeFibre F K p ↔ 𝔓.under (𝓞 F) = p :=
  Iff.rfl

end Induced

section RankinSelberg

variable {R : Type*} [CommRing R]


private theorem rsEulerPoly_eq_prod (α₁ α₂ β₁ β₂ β₃ : R) :
    rsEulerPoly (α₁ + α₂) (α₁ * α₂) (β₁ + β₂ + β₃) (β₁ * β₂ + β₁ * β₃ + β₂ * β₃)
        (β₁ * β₂ * β₃) =
      (C 1 - C (α₁ * β₁) * X) * (C 1 - C (α₁ * β₂) * X) * (C 1 - C (α₁ * β₃) * X) *
        ((C 1 - C (α₂ * β₁) * X) * (C 1 - C (α₂ * β₂) * X) * (C 1 - C (α₂ * β₃) * X)) := by
  simp only [rsEulerPoly, map_add, map_sub, map_neg, map_mul, map_pow, map_ofNat, map_one]
  ring

end RankinSelberg

end LanglandsTunnell.RankinSelberg

end
