import Mathlib

set_option autoImplicit false

namespace EisensteinWeightOne

def chiNegThree (n : ℕ) : ℤ :=
  if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

def sigmaChi (n : ℕ) : ℤ :=
  ∑ d ∈ n.divisors, chiNegThree d

def e1Chi3 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 6 * sigmaChi n

noncomputable def e1Chi3In (R : Type*) [CommRing R] : PowerSeries R :=
  PowerSeries.map (Int.castRingHom R) e1Chi3

open CongruenceSubgroup in

def E1Chi3IsModular : Prop :=
  ∃ f : ModularForm (Gamma1 3) 1, ∀ z : UpperHalfPlane,
    f z = ∑' n : ℕ,
      ((PowerSeries.coeff n e1Chi3 : ℤ) : ℂ) *
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * (z : ℂ))

end EisensteinWeightOne
