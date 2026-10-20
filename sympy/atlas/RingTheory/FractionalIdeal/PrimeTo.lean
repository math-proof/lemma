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

/-- A product of fractional ideals prime to J is prime to J. -/
theorem IsPrimeTo.mul {I K : FractionalIdeal A⁰ (FractionRing A)}
    {J : Ideal A} (hI : I.IsPrimeTo J) (hK : K.IsPrimeTo J) :
    (I * K).IsPrimeTo J := by
  intro p _ hp
  rw [FractionalIdeal.extended_mul, hI p hp, hK p hp, one_mul]

/-- The inverse of an invertible fractional ideal prime to J is prime to J. -/
theorem IsPrimeTo.inv_unit
    {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} {J : Ideal A}
    (hu : (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J) :
    ((u⁻¹ : (FractionalIdeal A⁰ (FractionRing A))ˣ) :
      FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J := by
  intro p _ hp
  have h1 : FractionalIdeal.extended (FractionRing A)
      (nonZeroDivisors_le_comap_algebraMap_atPrime p)
      (↑(u * u⁻¹) : FractionalIdeal A⁰ (FractionRing A)) = 1 := by
    simp [FractionalIdeal.extended_one]
  rw [Units.val_mul, FractionalIdeal.extended_mul, hu p hp, one_mul] at h1
  exact h1

/-- The subgroup of invertible fractional ideals prime to J. -/
def unitsPrimeTo (J : Ideal A) :
    Subgroup (FractionalIdeal A⁰ (FractionRing A))ˣ where
  carrier := {u | (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J}
  one_mem' := isPrimeTo_one J
  mul_mem' := fun ha hb => ha.mul hb
  inv_mem' := fun hu => hu.inv_unit

/-- Membership in unitsPrimeTo is the prime-to condition on the underlying fractional ideal. -/
@[simp]
theorem mem_unitsPrimeTo_iff {J : Ideal A}
    {u : (FractionalIdeal A⁰ (FractionRing A))ˣ} :
    u ∈ unitsPrimeTo J ↔
      (u : FractionalIdeal A⁰ (FractionRing A)).IsPrimeTo J :=
  Iff.rfl

/-- Being prime to an ideal implies being prime to every larger ideal. -/
theorem IsPrimeTo.mono {I : FractionalIdeal A⁰ (FractionRing A)}
    {J K : Ideal A} (hI : I.IsPrimeTo J) (hJK : J ≤ K) :
    I.IsPrimeTo K := by
  intro p _ hp
  exact hI p (hJK.trans hp)

/-- The prime-to subgroups are monotone in the ideal. -/
theorem unitsPrimeTo_mono {J K : Ideal A} (hJK : J ≤ K) :
    unitsPrimeTo J ≤ unitsPrimeTo K := by
  intro u hu
  exact hu.mono hJK

/-- Every invertible fractional ideal is prime to the top ideal. -/
@[simp]
theorem unitsPrimeTo_top : unitsPrimeTo (⊤ : Ideal A) = ⊤ := by
  rw [eq_top_iff]
  intro u _
  rw [mem_unitsPrimeTo_iff]
  intro p hpPrime hp
  exact (hpPrime.ne_top (top_unique hp)).elim

end FractionalIdeal
