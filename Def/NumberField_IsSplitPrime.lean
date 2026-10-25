import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.RamificationInertia.Galois

set_option autoImplicit false

namespace NumberField

open scoped NumberField nonZeroDivisors

variable (K M : Type*) [Field K] [NumberField K] [Field M] [NumberField M]
  [Algebra K M] [IsGalois K M]

def IsSplitPrime (𝔩 : Ideal (𝓞 K)) : Prop :=
  𝔩.IsMaximal ∧ (Ideal.absNorm 𝔩).Prime ∧
    Nat.card (𝔩.primesOver (𝓞 M)) = Module.finrank K M

end NumberField
