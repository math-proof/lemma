/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/CubicRecurrenceDiscriminant.lean -/

import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace MetaMathlibExt

/-! # Cubic-recurrence discriminant divisibility -/

/-- The cubic whose three roots are `R * (γᵢ + γᵢ⁻¹)` in the
Roettger–Williams construction. -/
def cubicRecurrenceRootCondition (S₁ S₂ R : ℤ) (γ : ℂ) : Prop :=
  let ρ := (R : ℂ) * (γ + γ⁻¹)
  let S₃ : ℤ := R * S₁ ^ 2 - 2 * R * S₂ - 4 * R ^ 3
  ρ ^ 3 - (S₁ : ℂ) * ρ ^ 2 + (S₂ : ℂ) * ρ - (S₃ : ℂ) = 0

/-- A pair of integer sequences satisfying the source's explicit algebraic
definitions. The witnesses `γ₁, γ₂, γ₃` are the distinct nonunit parameters
whose product is one and whose associated `R * (γᵢ + γᵢ⁻¹)` values are the
three roots of the source cubic. The equations then determine every value of
`U` and `W`; the `U` equation is denominator-cleared and starts at `n = 1`,
while `U 0 = 0` is specified separately. -/
def IsCubicRecurrencePair
    (S₁ S₂ R : ℤ) (U W : ℕ → ℤ) : Prop :=
  ∃ γ₁ γ₂ γ₃ : ℂ,
    γ₁ ≠ 1 ∧ γ₂ ≠ 1 ∧ γ₃ ≠ 1 ∧
    γ₁ ≠ γ₂ ∧ γ₂ ≠ γ₃ ∧ γ₃ ≠ γ₁ ∧
    γ₁ * γ₂ * γ₃ = 1 ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₁ ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₂ ∧
    cubicRecurrenceRootCondition S₁ S₂ R γ₃ ∧
    U 0 = 0 ∧
    (∀ n : ℕ, 1 ≤ n →
      (U n : ℂ) * ((1 - γ₁) * (1 - γ₂) * (1 - γ₃)) =
        (R : ℂ) ^ (n - 1) *
          ((1 - γ₁ ^ n) * (1 - γ₂ ^ n) * (1 - γ₃ ^ n))) ∧
    ∀ n : ℕ,
      (W n : ℂ) =
        (R : ℂ) ^ n *
          ((1 + γ₁ ^ n) * (1 + γ₂ ^ n) * (1 + γ₃ ^ n) - 2)

/-- The source discriminant sequence `Dₙ = gcd(Wₙ - 6Rⁿ, Uₙ)`. -/
def cubicRecurrenceDiscriminant (R : ℤ) (U W : ℕ → ℤ) (n : ℕ) : ℕ :=
  Nat.gcd (W n - 6 * R ^ n).natAbs (U n).natAbs

private noncomputable def newtonP (S : Type*) [CommRing S] (a b c : S) : ℕ → S
  | 0 => 1 + 1 + 1
  | 1 => a
  | 2 => a ^ 2 - 2 * b
  | (k + 3) => a * newtonP S a b c (k + 2) - b * newtonP S a b c (k + 1) + c * newtonP S a b c k

private noncomputable def newtonQ (S : Type*) [CommRing S] (x y r : S) : ℕ → S
  | 0 => 0
  | 1 => 1
  | 2 => x + y + 2 * r
  | (k + 3) => y * newtonQ S x y r (k + 2) - r * x * newtonQ S x y r (k + 1)
      + r ^ 3 * newtonQ S x y r k
      + (newtonP S x (r * y) (r ^ 3) (k + 2) + r * newtonP S x (r * y) (r ^ 3) (k + 1))
end MetaMathlibExt
