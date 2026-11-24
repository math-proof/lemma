module
public import Mathlib
public import Theorem.HahnSeries.X0ModL
public import Def.AlgebraicCurve_Correspondence
public import Theorems.Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed
public import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
set_option autoImplicit false


public section

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve Polynomial

namespace ModularCurve


section FrobeniusEndomorphism

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

variable {K N ℓ} in
def frobeniusModLRingHom : modularFunctionFieldFullC K N →+* modularFunctionFieldFullC K N where
  toFun x := ⟨qExpand K ℓ (x : LaurentSeries K), qExpand_mem_modularFunctionFieldFullC x.2⟩
  map_one' := Subtype.ext (map_one (qExpand K ℓ))
  map_mul' _ _ := Subtype.ext (map_mul (qExpand K ℓ) _ _)
  map_zero' := Subtype.ext (map_zero (qExpand K ℓ))
  map_add' _ _ := Subtype.ext (map_add (qExpand K ℓ) _ _)

def frobeniusModL : modularFunctionFieldFullC K N →ₐ[K] modularFunctionFieldFullC K N :=
  { frobeniusModLRingHom K N ℓ with
    commutes' := fun a => Subtype.ext <| by
      show qExpand K ℓ (algebraMap K (LaurentSeries K) a) = algebraMap K (LaurentSeries K) a
      rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero] }

end FrobeniusEndomorphism

section PlacesDivisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def frobeniusPlaceModL (w : Place K (modularFunctionFieldFullC K N)) :
    Place K (modularFunctionFieldFullC K N) :=
  w.restrictAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

def frobeniusDivPushforwardModL :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  Divisor.pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

def frobeniusDivPullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)] :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  Divisor.pullbackAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)

end PlacesDivisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def FrobeniusInputsModL : Prop :=
  ∃ (_ : HasPrincipalDivisors K (modularFunctionFieldFullC K N))
    (hfin : FiniteAlong K (frobeniusModL K N ℓ)),
    FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) ∧
      NormFormulaAlong K (frobeniusModL K N ℓ) hfin

variable {K N ℓ} in

def frobeniusDegZeroPushforwardModL :
    Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) →+
      Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) :=
  ((frobeniusDivPushforwardModL K N ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pushforwardAlong_mem_degZero (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) D.2

def frobeniusDegZeroPullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)) :
    Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) →+
      Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N) :=
  ((frobeniusDivPullbackModL K N ℓ).domRestrict _).codRestrict _
    fun D => Divisor.pullbackAlong_mem_degZero (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
      hFI D.2

def frobeniusPic0PushforwardModL (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin) : JZeroC K N →+ JZeroC K N :=
  QuotientAddGroup.map _ _ (frobeniusDegZeroPushforwardModL K N ℓ) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pushforwardAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)
      hfin hN hD)

def frobeniusPic0PullbackModL [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ)) :
    JZeroC K N →+ JZeroC K N :=
  QuotientAddGroup.map _ _ (frobeniusDegZeroPullbackModL K N ℓ hFI) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact Divisor.isPrincipal_pullbackAlong (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ) hD)

open Classical in

def frobeniusPushforwardModL : JZeroC K N →+ JZeroC K N :=
  if h : FrobeniusInputsModL K N ℓ then
    frobeniusPic0PushforwardModL K N ℓ h.snd.fst h.snd.snd.2
  else 0

open Classical in

def frobeniusPullbackModL : JZeroC K N →+ JZeroC K N :=
  if h : FrobeniusInputsModL K N ℓ then
    haveI := h.fst
    frobeniusPic0PullbackModL K N ℓ h.snd.snd.1
  else 0

variable {K N ℓ}

end Jacobian

end ModularCurve

end
