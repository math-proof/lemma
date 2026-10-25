import Mathlib
import Def.ModularCurve_HeckeOperatorTotal

set_option autoImplicit false

namespace ModularCurve

def HeckeInputsAll (N : ℕ) [NeZero N] : Prop :=
  ∀ ℓ : Nat.Primes,
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    HeckeInputsAlong (AlgebraicClosure ℚ) N ℓ

end ModularCurve
