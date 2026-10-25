import Mathlib
import Lemma.ModularCurve.FrobeniusModL
import Def.ModularCurve_HeckeOperatorModL

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Divisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]


theorem heckeDivOperatorModL_apply (D : Divisor K (modularFunctionFieldFullC K N)) :
    heckeDivOperatorModL K N ℓ D =
      frobeniusDivPushforwardModL K N ℓ D + frobeniusDivPullbackModL K N ℓ D :=
  rfl

end Divisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]


theorem heckeOperatorModL_apply (x : JZeroC K N) :
    heckeOperatorModL K N ℓ x = frobeniusPushforwardModL K N ℓ x + frobeniusPullbackModL K N ℓ x :=
  rfl

variable {K N ℓ}

theorem heckeOperatorModL_mk [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hfin : FiniteAlong K (frobeniusModL K N ℓ))
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (hN : NormFormulaAlong K (frobeniusModL K N ℓ) hfin)
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    heckeOperatorModL K N ℓ (Pic0.mk D) =
      Pic0.mk (frobeniusDegZeroPushforwardModL K N ℓ D + frobeniusDegZeroPullbackModL K N ℓ hFI D) := by
  rw [heckeOperatorModL_apply, frobeniusPushforwardModL_mk hfin hFI hN,
    frobeniusPullbackModL_mk hfin hFI hN, Pic0.mk_add]

theorem coe_frobeniusDegZero_add [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]
    (hFI : FundamentalIdentityAlong K (frobeniusModL K N ℓ) (frobeniusModL_isIntegral K N ℓ))
    (D : Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
    ((frobeniusDegZeroPushforwardModL K N ℓ D + frobeniusDegZeroPullbackModL K N ℓ hFI D :
        Divisor.degZero (K := K) (F := modularFunctionFieldFullC K N)) :
        Divisor K (modularFunctionFieldFullC K N)) =
      heckeDivOperatorModL K N ℓ (D : Divisor K (modularFunctionFieldFullC K N)) :=
  rfl

theorem heckeOperatorModL_of_not (h : ¬ FrobeniusInputsModL K N ℓ) : heckeOperatorModL K N ℓ = 0 := by
  rw [heckeOperatorModL, frobeniusPushforwardModL_of_not h, frobeniusPullbackModL_of_not h]
  exact add_zero (0 : JZeroC K N →+ JZeroC K N)

end Jacobian

end ModularCurve

end
