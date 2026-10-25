import Lemma.LanglandsTunnell.CubicInduction_Carrier
import Instance.LanglandsTunnell_CubicInduction_IotaTorus

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section DiagHom

variable {A : Type*} [CommRing A]

def diagUnitGL2 (x : Aˣ) : GL (Fin 2) A where
  val := !![(x : A), 0; 0, 1]
  inv := !![((x⁻¹ : Aˣ) : A), 0; 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

@[simp] theorem coe_diagUnitGL2 (x : Aˣ) :
    ((diagUnitGL2 x : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, 1] :=
  rfl

def diagHom : Aˣ →* GL (Fin 2) A where
  toFun := diagUnitGL2
  map_one' := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' x y := by
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem diagHom_apply (x : Aˣ) : diagHom x = diagUnitGL2 x :=
  rfl

end DiagHom

section RatTorus

variable (v : HeightOneSpectrum (𝓞 ℚ))

def ratPrimeAt : v.adicCompletion ℚ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ)

theorem ratPrimeAt_ne_zero : ratPrimeAt v ≠ 0 := by
  haveI : CharZero (v.adicCompletion ℚ) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
  have h : 1 < Ideal.absNorm v.asIdeal := NumberField.HeightOneSpectrum.one_lt_absNorm v
  exact Nat.cast_ne_zero.mpr (by omega)

def ratPrimeUnit : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 (ratPrimeAt v) (ratPrimeAt_ne_zero v)

def iotaTorusLocal (n : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagHom (ratPrimeUnit v ^ n))

@[simp] theorem iotaTorusLocal_zero : iotaTorusLocal v 0 = 1 := by
  simp only [iotaTorusLocal, pow_zero, map_one]

theorem iotaTorusLocal_add (m n : ℕ) :
    iotaTorusLocal v (m + n) = iotaTorusLocal v m * iotaTorusLocal v n := by
  simp only [iotaTorusLocal, pow_add, map_mul]

end RatTorus

section Countable

variable (K : Type*) [Field K] [Countable K]

end Countable

end LanglandsTunnell.CubicInduction
