import Mathlib
import Def.LocalRing_PrincipalUnits

set_option autoImplicit false

namespace IsLocalRing


variable {R : Type*} [CommRing R] [IsLocalRing R]

theorem mem_principalUnits_iff {k : ℕ} {u : Rˣ} :
    u ∈ principalUnits R k ↔ (u : R) - 1 ∈ maximalIdeal R ^ k := Iff.rfl

@[simp] theorem principalUnits_zero : principalUnits R 0 = ⊤ := by
  ext u; simp [mem_principalUnits_iff]

theorem principalUnits_antitone : Antitone (principalUnits R) :=
  fun _ _ hkl _ hu => Ideal.pow_le_pow_right hkl hu

end IsLocalRing
