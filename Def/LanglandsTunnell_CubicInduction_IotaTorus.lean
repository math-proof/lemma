import Def.LanglandsTunnell_CubicInduction_Carrier
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

end DiagHom

section RatTorus

variable (v : HeightOneSpectrum (𝓞 ℚ))

def ratPrimeAt : v.adicCompletion ℚ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion ℚ)

def ratPrimeUnit : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 (ratPrimeAt v) (ratPrimeAt_ne_zero v)

def iotaTorusLocal (n : ℕ) : GL (Fin 3) (v.adicCompletion ℚ) :=
  iotaGL (diagHom (ratPrimeUnit v ^ n))

end RatTorus


end LanglandsTunnell.CubicInduction

end
