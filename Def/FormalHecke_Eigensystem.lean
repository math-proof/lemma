import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.Ring.Defs

set_option autoImplicit false

namespace FormalHecke

variable {R : Type*} [CommRing R]

def IsEigensystem (e a : ℕ → R) : Prop :=
  a 1 = 1 ∧ ∀ ℓ : ℕ, ℓ.Prime → ∀ n : ℕ,
    a (ℓ * n) + e ℓ * (if ℓ ∣ n then a (n / ℓ) else 0) = a ℓ * a n

def IsRecursive (e a : ℕ → R) : Prop :=
  a 1 = 1 ∧ (∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n) ∧
    ∀ ℓ r : ℕ, ℓ.Prime → a (ℓ ^ (r + 2)) = a ℓ * a (ℓ ^ (r + 1)) - e ℓ * a (ℓ ^ r)

end FormalHecke
