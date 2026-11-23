module

public import Theorem.Measure.TateGlobalZeta

@[expose] public section

set_option autoImplicit false

noncomputable section

open Complex

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

def normPowChar (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((ideleNorm F x : ℝ) : ℂ) ^ (I * t)) (ofReal_ideleNorm_cpow_ne_zero F x _)
  map_one' := Units.ext (by rw [Units.val_mk0, ideleNorm_one, ofReal_one, one_cpow, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg (ideleNorm_pos x).le (ideleNorm_pos y).le])

variable {F}

end NumberField.TateGlobal

end

end
