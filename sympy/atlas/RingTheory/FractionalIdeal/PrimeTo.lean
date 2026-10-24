/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/FractionalIdeal/PrimeTo.lean -/

import Mathlib.RingTheory.FractionalIdeal.Extended

/-!
# Fractional ideals prime to an ideal

A fractional ideal is prime to an ideal when it becomes the unit ideal after localization at
every prime containing that ideal. The invertible fractional ideals with this property form a
subgroup.
-/

open scoped nonZeroDivisors

@[expose] noncomputable section

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

/-- A fractional ideal is prime to J if it becomes one at every prime containing J. -/
def IsPrimeTo (I : FractionalIdeal A⁰ (FractionRing A)) (J : Ideal A) : Prop :=
  ∀ (p : Ideal A) [p.IsPrime], J ≤ p →
    FractionalIdeal.extended (FractionRing A)
      (nonZeroDivisors_le_comap_algebraMap_atPrime p) I = 1

/-- The unit fractional ideal is prime to every ideal. -/
@[simp]
theorem isPrimeTo_one (J : Ideal A) :
    IsPrimeTo (1 : FractionalIdeal A⁰ (FractionRing A)) J := by
  intro p _ _
  exact FractionalIdeal.extended_one _ _

/-- The subgroup of invertible fractional ideals prime to J. -/
def unitsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (FractionRing A))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J}
  one_mem' := isPrimeTo_one J
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun hu => hu.inv_unit
end FractionalIdeal
