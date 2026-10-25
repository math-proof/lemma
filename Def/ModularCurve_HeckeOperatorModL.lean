import Mathlib
import Lemma.ModularCurve.FrobeniusModL

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Divisors

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
variable [HasPrincipalDivisors K (modularFunctionFieldFullC K N)]

def heckeDivOperatorModL :
    Divisor K (modularFunctionFieldFullC K N) →+ Divisor K (modularFunctionFieldFullC K N) :=
  frobeniusDivPushforwardModL K N ℓ + frobeniusDivPullbackModL K N ℓ

end Divisors

section Jacobian

variable (K : Type*) [Field K] (N : ℕ) (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]

def heckeOperatorModL : JZeroC K N →+ JZeroC K N :=
  frobeniusPushforwardModL K N ℓ + frobeniusPullbackModL K N ℓ

end Jacobian

end ModularCurve

end
