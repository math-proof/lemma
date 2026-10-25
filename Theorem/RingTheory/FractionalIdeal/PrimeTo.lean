/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended
open scoped nonZeroDivisors

@[expose] noncomputable section

/-!
# Fractional ideals prime to an ideal

A fractional ideal is prime to an ideal when it becomes the unit ideal after localization at
every prime containing that ideal. The invertible fractional ideals with this property form a
subgroup.
-/


namespace FractionalIdeal

variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
/-- Nonzero divisors remain nonzero after mapping to the localization at a prime. -/
theorem nonZeroDivisors_le_comap_algebraMap_atPrime
    (p : Ideal A) [p.IsPrime] :
    A⁰ ≤ Submonoid.comap (algebraMap A (Localization.AtPrime p))
      (Localization.AtPrime p)⁰ := by
  intro a ha
  rw [Submonoid.mem_comap]
  exact IsLocalization.map_nonZeroDivisors_le p.primeCompl
    (Localization.AtPrime p) ⟨a, ha, rfl⟩

end FractionalIdeal
