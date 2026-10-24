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

structure IsLocalReciprocityMap (i : K →+* M) (H : Type*) [Group H] [MulSemiringAction H M] (θ : Kˣ →* H) : Prop where

  surjective : Function.Surjective θ

  apply_eq_one_iff : ∀ a : Kˣ, θ a = 1 ↔ ∃ b : M, (∏ᶠ h : H, h • b) = i (a : K)

  mem_of_finprod_quotient_smul_eq : ∀ (H' : Subgroup H) (a : Kˣ) (b : M), (∀ h ∈ H', h • b = b) →
    (∏ᶠ c : H ⧸ H', (Quotient.out c) • b) = i (a : K) → θ a ∈ H'

  image_units_eq_inertiaSet : (⇑θ) '' {a : Kˣ | Valued.v (a : K) = 1} = inertiaSet M H

  mul_zpow_neg_mem_inertiaSet : ∀ (φ : H), IsArithFrobenius K M H φ →
    ∀ (a : Kˣ) (n : ℤ), Valued.v (a : K) = WithZero.exp (-n) → θ a * φ ^ (-n) ∈ inertiaSet M H

end LocalReciprocity
