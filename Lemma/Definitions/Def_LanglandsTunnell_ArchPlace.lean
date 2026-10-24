import Lemma.Definitions.Def_LanglandsTunnell_TateLocalZeta

noncomputable section

open Complex Real MeasureTheory LanglandsTunnell.TateLocal

namespace LanglandsTunnell.ArchPlace

def psiComplex : AddChar ℂ ℂ where
  toFun z := Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z)))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by
    rw [← Complex.exp_add, map_add]; ring_nf

theorem psiComplex_apply (z : ℂ) :
    psiComplex z = Complex.exp (-(2 * π * Complex.I * (z + starRingEnd ℂ z))) := rfl

def anglePhase (z : ℂˣ) : ℂ := (z : ℂ) / (‖(z : ℂ)‖ : ℂ)

@[simp] theorem norm_anglePhase (z : ℂˣ) : ‖anglePhase z‖ = 1 := by
  rw [anglePhase, norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr z.ne_zero)]

theorem anglePhase_ne_zero (z : ℂˣ) : anglePhase z ≠ 0 := fun h => by
  have := norm_anglePhase z; rw [h, norm_zero] at this; exact one_ne_zero this.symm

theorem anglePhase_mul (z w : ℂˣ) : anglePhase (z * w) = anglePhase z * anglePhase w := by
  simp only [anglePhase, Units.val_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv]
  ring

def complexCharFun (u : ℂ) (k : ℤ) : ℂˣ →* ℂˣ where
  toFun z := Units.mk0 (((‖(z : ℂ)‖ : ℂ) ^ (2 * u)) * anglePhase z ^ k)
    (mul_ne_zero
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr z.ne_zero))))
      (zpow_ne_zero _ (anglePhase_ne_zero z)))
  map_one' := by ext; simp [anglePhase]
  map_mul' z w := by
    ext
    simp only [Units.val_mul, Units.val_mk0]
    push_cast [norm_mul, anglePhase_mul, mul_zpow]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

theorem complexCharFun_apply (u : ℂ) (k : ℤ) (z : ℂˣ) :
    ((complexCharFun u k z : ℂˣ) : ℂ) = (‖(z : ℂ)‖ : ℂ) ^ (2 * u) * anglePhase z ^ k := rfl

def complexTestFun (k : ℤ) : ℂ → ℂ :=
  fun z => (starRingEnd ℂ z) ^ k.toNat * z ^ (-k).toNat * Complex.exp (-(2 * π * ‖z‖ ^ 2))

@[simp] theorem complexTestFun_zero_apply (z : ℂ) :
    complexTestFun 0 z = Complex.exp (-(2 * π * ‖z‖ ^ 2)) := by
  simp [complexTestFun]

theorem complexTestFun_zero_at_zero : complexTestFun 0 0 = 1 := by simp

theorem complexTestFun_zero_ne_zero : complexTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def complexZeta (μ : Measure ℂ) (f : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ z, f z * charExt χ z * ((‖z‖ : ℂ) ^ ((2 : ℂ) * s - 2)) ∂μ

def complexGammaAt (μ : Measure ℂ) (ψ : AddChar ℂ ℂ) (f₀ : ℂ → ℂ) (χ : ℂˣ →* ℂˣ) (s : ℂ) : ℂ :=
  complexZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / complexZeta μ f₀ χ s

theorem psiComplex_mul_eq (z w : ℂ) :
    psiComplex (z * w)
      = Complex.exp (-(2 * π * Complex.I * (z * w + starRingEnd ℂ z * starRingEnd ℂ w))) := by
  rw [psiComplex_apply, map_mul]

def psiReal : AddChar ℝ ℂ where
  toFun x := Complex.exp (-(2 * π * Complex.I * x))
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by push_cast; rw [← Complex.exp_add]; ring_nf

theorem psiReal_apply (x : ℝ) : psiReal x = Complex.exp (-(2 * π * Complex.I * x)) := rfl

def realSign (x : ℝˣ) : ℂˣ :=
  Units.mk0 ((x : ℝ) / (‖(x : ℝ)‖ : ℝ) : ℂ) (by
    have hx : (x : ℝ) ≠ 0 := x.ne_zero
    simp only [ne_eq, Complex.ofReal_eq_zero, div_eq_zero_iff, hx, norm_eq_zero, or_self,
      not_false_eq_true])

theorem realSign_mul (x y : ℝˣ) : realSign (x * y) = realSign x * realSign y := by
  ext
  simp only [realSign, Units.val_mk0, Units.val_mul, norm_mul]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv]; ring

def realCharFun (u : ℂ) (a : ZMod 2) : ℝˣ →* ℂˣ where
  toFun x := Units.mk0 ((‖(x : ℝ)‖ : ℂ) ^ u)
      (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))))
    * realSign x ^ (a.val : ℕ)
  map_one' := by ext; simp [realSign]
  map_mul' x y := by
    ext
    simp only [Units.val_mul, Units.val_mk0, Units.val_pow_eq_pow_val, realSign_mul, mul_pow]
    push_cast [norm_mul]
    rw [Complex.mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
    ring

def realTestFun (a : ZMod 2) : ℝ → ℂ :=
  fun x => ((x : ℂ) ^ (a.val : ℕ)) * Complex.exp (-(π * x ^ 2))

@[simp] theorem realTestFun_zero_apply (x : ℝ) :
    realTestFun 0 x = Complex.exp (-(π * x ^ 2)) := by simp [realTestFun]

theorem realTestFun_zero_at_zero : realTestFun 0 0 = 1 := by simp

theorem realTestFun_zero_ne_zero : realTestFun 0 ≠ 0 := by
  intro h; have := congrFun h 0; simp at this

def realZeta (μ : Measure ℝ) (f : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  ∫ x, f x * charExt χ x * ((‖x‖ : ℂ) ^ (s - 1)) ∂μ

def realGammaAt (μ : Measure ℝ) (ψ : AddChar ℝ ℂ) (f₀ : ℝ → ℂ) (χ : ℝˣ →* ℂˣ) (s : ℂ) : ℂ :=
  realZeta μ (tateFourier ψ μ f₀) χ⁻¹ (1 - s) / realZeta μ f₀ χ s

end LanglandsTunnell.ArchPlace
