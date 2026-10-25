import Instance.NarrowRayClassGroup
import Mathlib.RingTheory.DedekindDomain.Different

set_option autoImplicit false

noncomputable section

namespace M4aP2

open Real NumberField NumberField.InfinitePlace Deep.NTSupply
open scoped nonZeroDivisors Classical

variable (K : Type) [Field K] [NumberField K]

def signAt (S : Finset {w : InfinitePlace K // IsReal w}) (x : K) : ℂ :=
  ∏ v ∈ S, ((SignType.sign (embedding_of_isReal v.2 x) : ℤ) : ℂ)

variable (𝔣 : Ideal (𝓞 K)) (χ : NarrowRayClassGroup K 𝔣 →* ℂ)

def chiIdeal (I : FractionalIdeal (𝓞 K)⁰ K) : ℂ :=
  if h : I ≠ 0 then
    (if hc : Units.mk0 I h ∈ coprimeToModulus K 𝔣
      then χ (NarrowRayClassGroup.mk K 𝔣 ⟨Units.mk0 I h, hc⟩) else 0)
  else 0

def IsParity (S : Finset {w : InfinitePlace K // IsReal w}) : Prop :=
  ∀ α : 𝓞 K, α ≠ 0 → α - 1 ∈ 𝔣 →
    chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) = signAt K S (α : K)

def chiFin (S : Finset {w : InfinitePlace K // IsReal w}) (α : 𝓞 K) : ℂ :=
  chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) * signAt K S (α : K)

def IsPrimitiveMod : Prop :=
  ∀ 𝔣' : Ideal (𝓞 K), 𝔣 ≤ 𝔣' → 𝔣' ≠ 𝔣 →
    ∃ α : 𝓞 K, α ≠ 0 ∧ α - 1 ∈ 𝔣' ∧ (∀ τ : K →+* ℝ, 0 < τ (α : K)) ∧
      chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 ∧
      chiIdeal K 𝔣 χ ((Ideal.span {α} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) ≠ 1

def addChar (x : K) : ℂ :=
  Complex.exp (2 * π * Complex.I * (Algebra.trace ℚ K x : ℂ))

def gaussSumAt (h𝔣 : 𝔣 ≠ ⊥) (S : Finset {w : InfinitePlace K // IsReal w}) (y : K) : ℂ :=
  haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔣 h𝔣
  haveI : Fintype (𝓞 K ⧸ 𝔣) := Fintype.ofFinite _
  signAt K S y
    * chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K)
        * ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K))
    * ∑ r : 𝓞 K ⧸ 𝔣, chiFin K 𝔣 χ S (Quotient.out r) * addChar K ((Quotient.out r : 𝓞 K) * y)

def IsGaussDatum (y : K) : Prop :=
  y ≠ 0 ∧ (∀ α : 𝓞 K, α ∈ 𝔣 → (Algebra.trace ℚ K ((α : K) * y) : ℚ) ∈ (algebraMap ℤ ℚ).range) ∧
    chiIdeal K 𝔣 χ (FractionalIdeal.spanSingleton (𝓞 K)⁰ y * (𝔣 : FractionalIdeal (𝓞 K)⁰ K)
        * ((differentIdeal ℤ (𝓞 K) : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0

end M4aP2

end
