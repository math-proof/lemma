/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeSupport.lean -/

import Mathlib.Data.Nat.Prime.Basic

namespace Nat

/-- `SamePrimeSupport a b` states that `a` and `b` are divisible
    by exactly the same prime numbers. -/
def SamePrimeSupport (a b : ℕ) : Prop := ∀ p : ℕ, p.Prime → (p ∣ a ↔ p ∣ b)
end Nat
