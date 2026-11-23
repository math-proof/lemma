module

public import Mathlib
public import Def.ModularCurve_X1
public import Theorem.LaurentSeries.FrobeniusModL

@[expose] public section

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve Polynomial

namespace ModularCurve


section FrobeniusEndomorphism

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

variable {K Γ ℓ} in
def qExpFrobeniusModLRingHom : qExpFunctionFieldC K Γ →+* qExpFunctionFieldC K Γ where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), qExpand_mem_qExpFunctionFieldC x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)

def qExpFrobeniusModL : qExpFunctionFieldC K Γ →ₐ[K] qExpFunctionFieldC K Γ :=
  { qExpFrobeniusModLRingHom K Γ ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

end FrobeniusEndomorphism

section PlacesDivisors

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def qExpFrobeniusPlaceModL (w : Place K (qExpFunctionFieldC K Γ)) : Place K (qExpFunctionFieldC K Γ) :=
  w.restrictAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

def qExpFrobeniusDivPushforwardModL :
    Divisor K (qExpFunctionFieldC K Γ) →+ Divisor K (qExpFunctionFieldC K Γ) :=
  Divisor.pushforwardAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

def qExpFrobeniusDivPullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)] :
    Divisor K (qExpFunctionFieldC K Γ) →+ Divisor K (qExpFunctionFieldC K Γ) :=
  Divisor.pullbackAlong (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)

end PlacesDivisors

section Jacobian

variable (K : Type*) [Field K] (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
variable (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def QExpFrobeniusInputsModL : Prop :=
  ∃ (_ : HasPrincipalDivisors K (qExpFunctionFieldC K Γ))
    (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ)),
    FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ) ∧
      NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin

variable {K Γ ℓ} in

def qExpFrobeniusDegZeroPushforwardModL :
    Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) →+
      Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) :=
  ((qExpFrobeniusDivPushforwardModL K Γ ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pushforwardAlong_mem_degZero (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) D.2

def qExpFrobeniusDegZeroPullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)) :
    Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) →+
      Divisor.degZero (K := K) (F := qExpFunctionFieldC K Γ) :=
  ((qExpFrobeniusDivPullbackModL K Γ ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pullbackAlong_mem_degZero (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hFI D.2

def qExpFrobeniusPic0PushforwardModL (hfin : FiniteAlong K (qExpFrobeniusModL K Γ ℓ))
    (hN : NormFormulaAlong K (qExpFrobeniusModL K Γ ℓ) hfin) :
    Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  QuotientAddGroup.map _ _ (qExpFrobeniusDegZeroPushforwardModL K Γ ℓ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hfin hN hD)

def qExpFrobeniusPic0PullbackModL [HasPrincipalDivisors K (qExpFunctionFieldC K Γ)]
    (hFI : FundamentalIdentityAlong K (qExpFrobeniusModL K Γ ℓ) (qExpFrobeniusModL_isIntegral K Γ ℓ)) :
    Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  QuotientAddGroup.map _ _ (qExpFrobeniusDegZeroPullbackModL K Γ ℓ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong (qExpFrobeniusModL K Γ ℓ)
      (qExpFrobeniusModL_isIntegral K Γ ℓ) hD)

open Classical in

def qExpFrobeniusPushforwardModL : Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  if h : QExpFrobeniusInputsModL K Γ ℓ then
    qExpFrobeniusPic0PushforwardModL K Γ ℓ h.snd.fst h.snd.snd.2
  else 0

open Classical in

def qExpFrobeniusPullbackModL : Pic0 K (qExpFunctionFieldC K Γ) →+ Pic0 K (qExpFunctionFieldC K Γ) :=
  if h : QExpFrobeniusInputsModL K Γ ℓ then
    haveI := h.fst
    qExpFrobeniusPic0PullbackModL K Γ ℓ h.snd.snd.1
  else 0

variable {K Γ ℓ}

end Jacobian

end ModularCurve

end
