import Mathlib

set_option autoImplicit false

noncomputable section

namespace ClassFunction

variable {G : Type*} [Group G] [Fintype G] {K : Type*} [Field K]

open scoped Classical in

def induced (H : Subgroup G) (φ : G → K) : G → K :=
  fun g => (Nat.card H : K)⁻¹ * ∑ x : G, if x⁻¹ * g * x ∈ H then φ (x⁻¹ * g * x) else 0

end ClassFunction

end
