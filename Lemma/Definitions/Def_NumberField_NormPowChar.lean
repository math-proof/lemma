import Lemma.Definitions.Def_NumberField_TateGlobalZeta

set_option autoImplicit false

noncomputable section

open Complex

namespace NumberField.TateGlobal

variable (F : Type) [Field F] [NumberField F]

theorem ideleNorm_one : ideleNorm F 1 = 1 := by
  have h := ideleNorm_mul (1 : (AdeleRing (𝓞 F) F)ˣ) 1
  rw [mul_one] at h
  exact (mul_eq_left₀ (ideleNorm_pos (1 : (AdeleRing (𝓞 F) F)ˣ)).ne').mp h.symm

theorem ofReal_ideleNorm_cpow_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ) :
    ((ideleNorm F x : ℝ) : ℂ) ^ s ≠ 0 := fun h =>
  (ideleNorm_pos x).ne' (ofReal_eq_zero.mp ((cpow_eq_zero_iff _ _).mp h).1)

def normPowChar (t : ℝ) : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ where
  toFun x := Units.mk0 (((ideleNorm F x : ℝ) : ℂ) ^ (I * t)) (ofReal_ideleNorm_cpow_ne_zero F x _)
  map_one' := Units.ext (by rw [Units.val_mk0, ideleNorm_one, ofReal_one, one_cpow, Units.val_one])
  map_mul' x y := Units.ext (by
    rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0, ideleNorm_mul, ofReal_mul,
      mul_cpow_ofReal_nonneg (ideleNorm_pos x).le (ideleNorm_pos y).le])

variable {F}

theorem coe_normPowChar_apply (t : ℝ) (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((normPowChar F t x : ℂˣ) : ℂ) = ((ideleNorm F x : ℝ) : ℂ) ^ (I * t) := rfl

theorem norm_coe_normPowChar_apply (t : ℝ) (x : (AdeleRing (𝓞 F) F)ˣ) : ‖((normPowChar F t x : ℂˣ) : ℂ)‖ = 1 := by
  rw [coe_normPowChar_apply, norm_cpow_eq_rpow_re_of_pos (ideleNorm_pos x), mul_re, I_re, I_im, ofReal_re, ofReal_im,
    zero_mul, one_mul, sub_zero, Real.rpow_zero]

theorem normPowChar_zero : normPowChar F 0 = 1 := by
  refine MonoidHom.ext fun x => Units.ext ?_
  rw [coe_normPowChar_apply, ofReal_zero, mul_zero, cpow_zero, MonoidHom.one_apply, Units.val_one]

theorem normPowChar_eq_one_of_ideleNorm_eq_one (t : ℝ) {x : (AdeleRing (𝓞 F) F)ˣ} (hx : ideleNorm F x = 1) :
    normPowChar F t x = 1 :=
  Units.ext (by rw [coe_normPowChar_apply, hx, ofReal_one, one_cpow, Units.val_one])

end NumberField.TateGlobal

end
