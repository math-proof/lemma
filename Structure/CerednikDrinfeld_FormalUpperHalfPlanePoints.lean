import Mathlib
import Lemma.CerednikDrinfeld.FormalUpperHalfPlaneFunctor
import Def.CerednikDrinfeld_OmegaTubes

set_option autoImplicit false

noncomputable section

open scoped TensorProduct MatrixGroups
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega

section ChartLoci

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable {B : Type} [CommRing B] [Algebra 𝒪 B]


end ChartLoci

section AdicPoints

variable {𝒪 : Type} [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (R : Type) [CommRing R] [Algebra 𝒪 R]

abbrev modPow (n : ℕ) : Type := R ⧸ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)}

theorem span_pow_succ_le (n : ℕ) :
    Ideal.span {algebraMap 𝒪 R π ^ (n + 1 + 1)} ≤ Ideal.span {algebraMap 𝒪 R π ^ (n + 1)} :=
  Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow _ (Nat.le_succ _))

def modPowTransition (n : ℕ) : modPow π R (n + 1) →ₐ[𝒪] modPow π R n :=
  Ideal.Quotient.factorₐ 𝒪 (span_pow_succ_le π R n)


structure AdicPoint : Type where

  pt : ∀ n : ℕ, OmegaObj (K := K) π (modPow π R n)

  compat : ∀ n : ℕ, DeligneDatum.map π (modPowTransition π R n) (pt (n + 1)) = pt n


variable {K π R}


variable (C : Type) [Field C] [Algebra R C]


open Classical in


end AdicPoints

section Sigma

variable (K₀ : Type) [Field K₀] {C : Type} [Field C] [Algebra K₀ C]
variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]

omit Γ₀ in


variable (ϖ : Omega.PseudoUniformizer K₀ C)


end Sigma

end FormalOmega
end CerednikDrinfeld

end
