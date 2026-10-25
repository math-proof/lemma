import Mathlib

set_option autoImplicit false

namespace LocalReciprocity

variable (K M : Type*) [Field K] [Field M]
  [Valued K (WithZero (Multiplicative ℤ))] [Valued M (WithZero (Multiplicative ℤ))]

def inertiaSet (H : Type*) [Group H] [MulSemiringAction H M] : Set H :=
  {h : H | ∀ x : M, Valued.v x ≤ 1 → Valued.v (h • x - x) < 1}

def IsArithFrobenius (H : Type*) [Group H] [MulSemiringAction H M] (φ : H) : Prop :=
  ∀ x : M, Valued.v x ≤ 1 →
    Valued.v (φ • x - x ^ Nat.card (IsLocalRing.ResidueField ((Valued.v (R := K)).valuationSubring))) < 1

end LocalReciprocity
