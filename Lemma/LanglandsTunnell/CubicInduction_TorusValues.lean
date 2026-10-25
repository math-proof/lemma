import Def.LanglandsTunnell_CubicInduction_HeckeDatum
import Lemma.LanglandsTunnell.CubicInduction_IotaTorus
import Def.LanglandsTunnell_CubicInduction_TorusValues

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix
open LanglandsTunnell.RankinSelberg

noncomputable section

namespace LanglandsTunnell.CubicInduction


section TwoRowPoint

variable {A : Type*} [CommRing A]


@[simp] theorem coe_diagUnits2 (x y : Aˣ) :
    ((diagUnits2 x y : GL (Fin 2) A) : Matrix (Fin 2) (Fin 2) A) = !![(x : A), 0; 0, (y : A)] :=
  rfl

theorem diagUnits2_one_right (x : Aˣ) : diagUnits2 x 1 = diagUnitGL2 x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagUnits2, diagUnitGL2]

variable (v : HeightOneSpectrum (𝓞 ℚ))


theorem twoRowPointLocal_zero_right (k : ℕ) : twoRowPointLocal v k 0 = iotaTorusLocal v k := by
  simp only [twoRowPointLocal, iotaTorusLocal, pow_zero, diagUnits2_one_right, diagHom_apply]

end TwoRowPoint

section Clause

variable {K : Type} [Field K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]


theorem not_hasSphericalTorusValuesAt_zero (c : HeightOneSpectrum (𝓞 K) → ℂ)
    (v : HeightOneSpectrum (𝓞 ℚ)) : ¬ HasSphericalTorusValuesAt c v (fun _ => (0 : ℂ)) := by
  intro h
  have h0 := h.1 0
  simp [sphericalTorusValue] at h0

end Clause

end LanglandsTunnell.CubicInduction

end
