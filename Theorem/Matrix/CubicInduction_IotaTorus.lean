module

public import Theorem.Matrix.CubicInduction_Carrier
public import Instance.LanglandsTunnell_CubicInduction_IotaTorus

public noncomputable section

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DiagHom

variable {A : Type*} [CommRing A]


@[simp] public theorem coe_diagUnitGL2 (x : Aˣ) :
    ((diagUnitGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, 1] :=
  rfl


public theorem diagHom_apply (x : Aˣ) : diagHom x = diagUnitGL2 x :=
  rfl

end DiagHom

section RatTorus

variable (v : HeightOneSpectrum (𝓞 ℚ))


public theorem ratPrimeAt_ne_zero : ratPrimeAt v ≠ 0 := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)


@[simp] public theorem iotaTorusLocal_zero : iotaTorusLocal v 0 = 1 := by
  simp only [iotaTorusLocal, pow_zero, map_one]


public theorem iotaTorusLocal_add (m n : ℕ) :
    iotaTorusLocal v (m + n) = iotaTorusLocal v m * iotaTorusLocal v n := by
  simp only [iotaTorusLocal, pow_add, map_mul]

end RatTorus

section Countable

variable (K : Type*) [Field K] [Countable K]

end Countable

end LanglandsTunnell.CubicInduction
