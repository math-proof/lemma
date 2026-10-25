import Def.FLTPrelim_Ramification
import Instance.EllipticCurve_FrobeniusTrace
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

namespace ModularCurve

abbrev HeckeAlg : Type := MvPolynomial Nat.Primes ℤ

def heckeGen (ℓ : Nat.Primes) : HeckeAlg := MvPolynomial.X ℓ


section EigenIdeal

variable {k : Type*} [CommRing k]


end EigenIdeal

section Divisorial

variable {G : Type*} [Group G] (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction G J] [SMulCommClass G HeckeAlg J]

abbrev heckeTorsion (𝔪 : Ideal HeckeAlg) : Submodule HeckeAlg J :=
  Submodule.torsionBySet HeckeAlg J (𝔪 : Set HeckeAlg)


end Divisorial

section Forms

variable (𝕋 : Type*) [CommRing 𝕋] (J : Type*) [AddCommGroup J] [Module 𝕋 J] (𝔪 : Ideal 𝕋)

def MTorsionNeBot : Prop :=
  Submodule.torsionBySet 𝕋 J 𝔪 ≠ ⊥

end Forms

section LocalClauses

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

def UnramifiedOutside : Prop :=
  ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → σ • x = x

def FrobeniusQuadratic : Prop :=
  ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ¬ ℓ ∣ N * p →
    ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ →
        ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) →
          σ • σ • x - heckeGen ⟨ℓ, hℓ⟩ • (σ • x) + ℓ • x = 0


end LocalClauses

section MultiplicityOne

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

structure MultiplicityOneData (𝔪 : Ideal HeckeAlg) : Prop where
  isMaximal : 𝔪.IsMaximal
  resChar : (p : HeckeAlg) ∈ 𝔪
  finrank_two : Module.finrank (HeckeAlg ⧸ 𝔪) (heckeTorsion J 𝔪) = 2

end MultiplicityOne


section Support

variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]

def EigenformSupport (IsEig : Ideal HeckeAlg → Prop) : Prop :=
  ∀ 𝔪 : Ideal HeckeAlg, IsEig 𝔪 → ((p : HeckeAlg)) ∈ 𝔪 → MTorsionNeBot HeckeAlg J 𝔪

end Support

section Bundle

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

structure EichlerShimuraDataReduced (IsEig : Ideal HeckeAlg → Prop) : Prop where
  unramifiedOutside : UnramifiedOutside (K := K) (L := L) N p J
  frobeniusQuadratic : FrobeniusQuadratic (K := K) (L := L) N p J
  eigenformSupport : EigenformSupport p J IsEig

end Bundle

section Datum

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]
variable (J' : Type*) [AddCommGroup J'] [Module HeckeAlg J']

structure IsSpecialization (A : ValuationSubring L) (ℓ : ℕ) (sp : J →+ J') (F : J' →+ J') :
    Prop where

  hecke_comm : ∀ (T : HeckeAlg) (x : J), sp (T • x) = T • sp x

  inertia_comm : ∀ σ ∈ A.inertiaSubgroupIn K, ∀ x : J, sp (σ • x) = sp x

  frobenius_comm : ∀ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ → ∀ x : J, sp (σ • x) = F (sp x)

  injective_torsion : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → sp x = 0 → x = 0


end Datum

section Citation

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable (N p : ℕ) (J : Type*) [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]


end Citation

end ModularCurve
