import Mathlib
import Instance.Submodule_LocalBox
import Def.QuaternionAlgebra_Order

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField

namespace QuaternionAlgebra

variable {a b : ℚ}


def IsMaximalOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) : Prop :=
  IsOrder Λ ∧ ∀ Λ' : Submodule ℤ ℍ[ℚ, a, b], IsOrder Λ' → Λ ≤ Λ' → Λ' = Λ


def IsEichlerOrder (Λ : Submodule ℤ ℍ[ℚ, a, b]) (N : ℕ) : Prop :=
  ∃ Λ₁ Λ₂ : Submodule ℤ ℍ[ℚ, a, b], IsMaximalOrder Λ₁ ∧ IsMaximalOrder Λ₂ ∧ Λ = Λ₁ ⊓ Λ₂ ∧
    Λ.toAddSubgroup.relIndex Λ₁.toAddSubgroup = N


variable (a b) in

def IsDefiniteRamifiedExactlyAt (q : ℕ) : Prop :=
  a < 0 ∧ b < 0 ∧
    ∀ v : HeightOneSpectrum (𝓞 ℚ),
      (∀ x : ℍ[ℚ, a, b] ⊗[ℚ] v.adicCompletion ℚ, x ≠ 0 → IsUnit x) ↔ ((q : 𝓞 ℚ) ∈ v.asIdeal)

end QuaternionAlgebra
