import Mathlib

set_option autoImplicit false

namespace IsLocalRing

def principalUnits (R : Type*) [CommRing R] [IsLocalRing R] (k : ℕ) : Subgroup Rˣ where
  carrier := {u | (u : R) - 1 ∈ maximalIdeal R ^ k}
  one_mem' := by simp
  mul_mem' := by
    intro u v hu hv
    have h : ((u * v : Rˣ) : R) - 1 = ((u : R) - 1) * v + ((v : R) - 1) := by
      push_cast; ring
    rw [Set.mem_setOf_eq, h]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hu) hv
  inv_mem' := by
    intro u hu
    have h : ((u⁻¹ : Rˣ) : R) - 1 = -(((u⁻¹ : Rˣ) : R) * ((u : R) - 1)) := by
      rw [mul_sub, mul_one, Units.inv_mul, neg_sub]
    rw [Set.mem_setOf_eq, h]
    exact Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hu)

end IsLocalRing
