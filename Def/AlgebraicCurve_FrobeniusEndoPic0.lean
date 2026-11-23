module

public import Def.AlgebraicCurve_FrobeniusEndo

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve


section Descent

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP F ℓ]
variable (φ : F →ₐ[K] F)

def frobeniusPushforwardDegZero (hφ : φ.toRingHom.IsIntegral) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pushforwardAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pushforwardAlong_mem_degZero φ hφ D.2)

def IsFrobeniusEndo.pushforwardPic0 (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ)
    (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (frobeniusPushforwardDegZero φ hφ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong φ hφ hfin
      (h.normFormulaAlong hφ hfin hrank hsurj hf1) hD)

end Descent


section PullbackDescent

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
variable {ℓ : ℕ} [Fact ℓ.Prime] {φ : F →ₐ[K] F}

def IsFrobeniusEndo.frobeniusPullbackDegZero (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) :=
  ((Divisor.pullbackAlong φ hφ).domRestrict
    (Divisor.degZero (K := K) (F := F))).codRestrict _
    (fun D => Divisor.pullbackAlong_mem_degZero φ hφ
      (h.fundamentalIdentityAlong (Fact.out : ℓ.Prime).ne_zero hφ hrank hsurj hf1) D.2)

def IsFrobeniusEndo.pullbackPic0 (h : IsFrobeniusEndo ℓ φ)
    (hφ : φ.toRingHom.IsIntegral) (hrank : finrankAlong K φ = ℓ)
    (hsurj : Function.Surjective (Place.restrictAlong φ hφ))
    (hf1 : ∀ w : Place K F, Place.inertiaDegAlong φ hφ w = 1) :
    Pic0 K F →+ Pic0 K F :=
  QuotientAddGroup.map _ _ (h.frobeniusPullbackDegZero hφ hrank hsurj hf1) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong φ hφ hD)

end PullbackDescent

end AlgebraicCurve

end

end
