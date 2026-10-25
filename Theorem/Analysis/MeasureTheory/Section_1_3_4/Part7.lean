import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4.Part6


/-- Lemma 1.3.19 (Triangle inequality) -/

-- Helper: |∫f| ≤ ∫|f| for real absolutely integrable functions
lemma RealAbsolutelyIntegrable.abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) : |hf.integ| ≤ hf.abs.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  have h_pos_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.pos.1)
  have h_neg_nonneg := EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.neg.1)
  -- |a - b| ≤ a + b when a, b ≥ 0
  have h_abs_ineq : |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
                     (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal| ≤
                    (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
                    (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
    rw [abs_le]; constructor <;> linarith
  -- pos_fun + neg_fun = abs_fun pointwise
  have h_eq_pointwise : ∀ x, EReal.pos_fun f x + EReal.neg_fun f x = EReal.abs_fun f x := fun x => by
    simp only [EReal.pos_fun, EReal.neg_fun, EReal.abs_fun, ← EReal.coe_add]
    congr 1; rw [max_zero_add_max_neg_zero_eq_abs_self, Real.norm_eq_abs]
  have h_sum : UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f) =
               UnsignedLebesgueIntegral (EReal.abs_fun f) := by
    have h_eq_fun : EReal.pos_fun f + EReal.neg_fun f = EReal.abs_fun f := funext h_eq_pointwise
    rw [← h_eq_fun]; symm
    apply LowerUnsignedLebesgueIntegral.add hf.pos.1 hf.neg.1
    rw [h_eq_fun]; exact hf.abs.1
  have h_pos_ne_top := hf.pos.2.ne_top
  have h_neg_ne_top := hf.neg.2.ne_top
  have h_pos_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.pos.1))
  have h_neg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.neg.1))
  calc |(UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal -
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal|
      ≤ (UnsignedLebesgueIntegral (EReal.pos_fun f)).toReal +
        (UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := h_abs_ineq
    _ = (UnsignedLebesgueIntegral (EReal.pos_fun f) + UnsignedLebesgueIntegral (EReal.neg_fun f)).toReal := by
        rw [EReal.toReal_add h_pos_ne_top h_pos_ne_bot h_neg_ne_top h_neg_ne_bot]
    _ = (UnsignedLebesgueIntegral (EReal.abs_fun f)).toReal := by rw [h_sum]

-- Helper: ∫|Re(f)| ≤ ∫|f| for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.re_abs_integ_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.re.abs.integ ≤ hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  have h_le_pointwise : ∀ x, EReal.abs_fun (Complex.re_fun f) x ≤ EReal.abs_fun f x := fun x => by
    simp only [EReal.abs_fun, Complex.re_fun, EReal.coe_le_coe_iff, Real.norm_eq_abs]
    exact Complex.abs_re_le_norm (f x)
  have h_mono := LowerUnsignedLebesgueIntegral.mono hf.re.abs.1 hf.abs.1 (AlmostAlways.ofAlways h_le_pointwise)
  have h_re_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hf.re.abs.1))
  exact EReal.toReal_le_toReal h_mono h_re_ne_bot hf.abs.2.ne_top

-- Key identity for pos/neg parts under addition
-- (f+g)⁺ + f⁻ + g⁻ = f⁺ + g⁺ + (f+g)⁻
lemma Real.pos_neg_add_identity (a b : ℝ) :
    max (a + b) 0 + max (-a) 0 + max (-b) 0 =
    max a 0 + max b 0 + max (-(a + b)) 0 := by
  rcases le_or_gt a 0 with ha | ha <;> rcases le_or_gt b 0 with hb | hb
  · have hab : a + b ≤ 0 := add_nonpos ha hb
    rw [max_eq_right hab, max_eq_right ha, max_eq_right hb,
        max_eq_left (neg_nonneg.mpr ha), max_eq_left (neg_nonneg.mpr hb),
        max_eq_left (neg_nonneg.mpr hab)]
    ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_right ha, max_eq_left (le_of_lt hb),
          max_eq_left (neg_nonneg.mpr ha), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · rcases le_or_gt (a + b) 0 with hab | hab
    · rw [max_eq_right hab, max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_left (neg_nonneg.mpr hab)]
      ring
    · rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_right hb,
          max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_left (neg_nonneg.mpr hb),
          max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
      ring
  · have hab : 0 < a + b := add_pos ha hb
    rw [max_eq_left (le_of_lt hab), max_eq_left (le_of_lt ha), max_eq_left (le_of_lt hb),
        max_eq_right (neg_nonpos.mpr (le_of_lt ha)), max_eq_right (neg_nonpos.mpr (le_of_lt hb)),
        max_eq_right (neg_nonpos.mpr (le_of_lt hab))]
    ring

lemma EReal.pos_neg_add_identity {X: Type*} (f g : X → ℝ) :
    EReal.pos_fun (f + g) + EReal.neg_fun f + EReal.neg_fun g =
    EReal.pos_fun f + EReal.pos_fun g + EReal.neg_fun (f + g) := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.add_apply]
  have h := Real.pos_neg_add_identity (f x) (g x)
  simp only [← EReal.coe_add, h]

-- Key lemmas about pos_fun and neg_fun under scaling
lemma EReal.pos_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← mul_zero c, (mul_max_of_nonneg (f x) 0 hc).symm, mul_zero]

lemma EReal.neg_fun_smul_nonneg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: 0 ≤ c) :
    EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [show -(c * f x) = c * (-f x) from by ring]
  rw [← mul_zero c, (mul_max_of_nonneg (-f x) 0 hc).symm, mul_zero]

lemma EReal.pos_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show c * f x = (-c) * (-f x) from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (-f x) 0 hnc).symm, mul_zero]

lemma EReal.neg_fun_smul_neg {X: Type*} (f: X → ℝ) (c: ℝ) (hc: c < 0) :
    EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := by
  funext x
  simp only [EReal.pos_fun, EReal.neg_fun, Pi.smul_apply, smul_eq_mul]
  have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
  congr 1
  rw [show -(c * f x) = (-c) * f x from by ring]
  rw [← mul_zero (-c), (mul_max_of_nonneg (f x) 0 hnc).symm, mul_zero]

-- Helper: scalar multiplication linearity for real integral
lemma RealAbsolutelyIntegrable.integ_smul' {d:ℕ} {f: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (c: ℝ) : (hf.smul c).integ = c * hf.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]
  by_cases hc : 0 ≤ c
  · -- Case c ≥ 0
    have h_pos : EReal.pos_fun (c • f) = (c : EReal) • EReal.pos_fun f := EReal.pos_fun_smul_nonneg f c hc
    have h_neg : EReal.neg_fun (c • f) = (c : EReal) • EReal.neg_fun f := EReal.neg_fun_smul_nonneg f c hc
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = c * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hc
    rw [h_pos_scale, h_neg_scale, EReal.toReal_mul, EReal.toReal_mul, EReal.toReal_coe]
    ring
  · -- Case c < 0
    push_neg at hc
    have h_pos : EReal.pos_fun (c • f) = ((-c) : EReal) • EReal.neg_fun f := EReal.pos_fun_smul_neg f c hc
    have h_neg : EReal.neg_fun (c • f) = ((-c) : EReal) • EReal.pos_fun f := EReal.neg_fun_smul_neg f c hc
    have hnc : 0 ≤ -c := neg_nonneg.mpr (le_of_lt hc)
    have h_pos_scale : UnsignedLebesgueIntegral (EReal.pos_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.neg_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_pos]
      exact LowerUnsignedLebesgueIntegral.hom hf.neg.1 hnc
    have h_neg_scale : UnsignedLebesgueIntegral (EReal.neg_fun (c • f)) = (-c) * UnsignedLebesgueIntegral (EReal.pos_fun f) := by
      simp only [UnsignedLebesgueIntegral, h_neg]
      exact LowerUnsignedLebesgueIntegral.hom hf.pos.1 hnc
    rw [h_pos_scale, h_neg_scale]
    have : (-↑c : EReal) = ↑(-c) := rfl
    simp only [EReal.toReal_mul, this, EReal.toReal_coe]
    ring

-- Helper: addition linearity for real integral
lemma RealAbsolutelyIntegrable.integ_add' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.add hg).integ = hf.integ + hg.integ := by
  simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ]

  have h_id := EReal.pos_neg_add_identity f g

  -- Measurability
  have hpos_fg := (hf.add hg).pos.1
  have hneg_fg := (hf.add hg).neg.1
  have hpos_f := hf.pos.1
  have hneg_f := hf.neg.1
  have hpos_g := hg.pos.1
  have hneg_g := hg.neg.1

  -- Finiteness: ne_top
  have hpos_fg_ne_top := (hf.add hg).pos.2.ne_top
  have hneg_fg_ne_top := (hf.add hg).neg.2.ne_top
  have hpos_f_ne_top := hf.pos.2.ne_top
  have hneg_f_ne_top := hf.neg.2.ne_top
  have hpos_g_ne_top := hg.pos.2.ne_top
  have hneg_g_ne_top := hg.neg.2.ne_top

  -- Nonnegativity → not bot
  have hpos_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_fg))
  have hneg_fg_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_fg))
  have hpos_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_f))
  have hneg_f_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_f))
  have hpos_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hpos_g))
  have hneg_g_ne_bot := ne_of_gt (lt_of_lt_of_le EReal.bot_lt_zero (UnsignedLebesgueIntegral.nonneg hneg_g))

  simp only [UnsignedLebesgueIntegral] at *

  -- Apply integral additivity to the pointwise identity
  have h_lhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_fg hneg_f
                       (UnsignedMeasurable.add hpos_fg hneg_f)
  have h_lhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_fg hneg_f) hneg_g)
  have h_rhs_add1 := LowerUnsignedLebesgueIntegral.add hpos_f hpos_g
                       (UnsignedMeasurable.add hpos_f hpos_g)
  have h_rhs_add2 := LowerUnsignedLebesgueIntegral.add
                       (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg
                       (UnsignedMeasurable.add (UnsignedMeasurable.add hpos_f hpos_g) hneg_fg)

  -- From the identity, integrals are equal
  have h_integ_eq : LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun g) =
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
                    LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
                    LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g)) := by
    rw [← h_lhs_add1, ← h_lhs_add2, ← h_rhs_add1, ← h_rhs_add2, h_id]

  -- Convert to Real arithmetic
  have h1 : (LowerUnsignedLebesgueIntegral (EReal.pos_fun (f + g)) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun g)).toReal =
            (LowerUnsignedLebesgueIntegral (EReal.pos_fun f) +
             LowerUnsignedLebesgueIntegral (EReal.pos_fun g) +
             LowerUnsignedLebesgueIntegral (EReal.neg_fun (f + g))).toReal := by
    rw [h_integ_eq]

  -- Expand toReal_add using the finiteness conditions
  have hsum1_ne_top := EReal.add_ne_top hpos_fg_ne_top hneg_f_ne_top
  have hsum1_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_fg_ne_bot, hneg_f_ne_bot⟩
  have hsum2_ne_top := EReal.add_ne_top hpos_f_ne_top hpos_g_ne_top
  have hsum2_ne_bot := EReal.add_ne_bot_iff.mpr ⟨hpos_f_ne_bot, hpos_g_ne_bot⟩

  rw [EReal.toReal_add hsum1_ne_top hsum1_ne_bot hneg_g_ne_top hneg_g_ne_bot,
      EReal.toReal_add hpos_fg_ne_top hpos_fg_ne_bot hneg_f_ne_top hneg_f_ne_bot] at h1
  rw [EReal.toReal_add hsum2_ne_top hsum2_ne_bot hneg_fg_ne_top hneg_fg_ne_bot,
      EReal.toReal_add hpos_f_ne_top hpos_f_ne_bot hpos_g_ne_top hpos_g_ne_bot] at h1

  linarith

-- Helper: subtraction linearity for real integral
lemma RealAbsolutelyIntegrable.integ_sub' {d:ℕ} {f g: EuclideanSpace' d → ℝ}
    (hf: RealAbsolutelyIntegrable f) (hg: RealAbsolutelyIntegrable g) :
    (hf.sub hg).integ = hf.integ - hg.integ := by
  -- f - g = f + (-1) • g pointwise
  have heq : f - g = f + (-1 : ℝ) • g := by funext x; simp [sub_eq_add_neg]
  -- The integral depends only on function values
  have h_integ_eq : (hf.sub hg).integ = (hf.add (hg.smul (-1 : ℝ))).integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, heq]
  rw [h_integ_eq, RealAbsolutelyIntegrable.integ_add' (hf := hf) (hg := hg.smul _),
      RealAbsolutelyIntegrable.integ_smul' (hf := hg)]
  ring

-- Helper: scalar multiplication linearity for complex integral
lemma ComplexAbsolutelyIntegrable.integ_smul {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) : (hf.smul c).integ = c * hf.integ := by
  -- Expand the definition of complex integral
  simp only [ComplexAbsolutelyIntegrable.integ]
  -- Goal: (hf.smul c).re.integ + I * (hf.smul c).im.integ =
  --       c * (hf.re.integ + I * hf.im.integ)

  -- The function equalities (pointwise)
  have h_re_fun : Complex.re_fun (c • f) = c.re • Complex.re_fun f - c.im • Complex.im_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Complex.mul_re]
  have h_im_fun : Complex.im_fun (c • f) = c.re • Complex.im_fun f + c.im • Complex.re_fun f := by
    funext x
    simp only [Complex.re_fun, Complex.im_fun, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Complex.mul_im]

  -- Build the decomposed integrability proofs
  have h_re_decomp : RealAbsolutelyIntegrable (c.re • Complex.re_fun f - c.im • Complex.im_fun f) :=
    (hf.re.smul c.re).sub (hf.im.smul c.im)
  have h_im_decomp : RealAbsolutelyIntegrable (c.re • Complex.im_fun f + c.im • Complex.re_fun f) :=
    (hf.im.smul c.re).add (hf.re.smul c.im)

  -- The integrals of (hf.smul c).re and the decomposed form are equal
  -- because they're integrability proofs for the same function
  have h_re_integ : (hf.smul c).re.integ = h_re_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_re_fun]
  have h_im_integ : (hf.smul c).im.integ = h_im_decomp.integ := by
    simp only [RealAbsolutelyIntegrable.integ, UnsignedAbsolutelyIntegrable.integ, h_im_fun]

  -- Use linearity of real integral for the decomposed forms
  have h_re_linear : h_re_decomp.integ = c.re * hf.re.integ - c.im * hf.im.integ := by
    rw [show h_re_decomp = (hf.re.smul c.re).sub (hf.im.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_sub' (hf := hf.re.smul c.re) (hg := hf.im.smul c.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.re),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.im)]
  have h_im_linear : h_im_decomp.integ = c.re * hf.im.integ + c.im * hf.re.integ := by
    rw [show h_im_decomp = (hf.im.smul c.re).add (hf.re.smul c.im) from rfl]
    rw [RealAbsolutelyIntegrable.integ_add' (hf := hf.im.smul c.re) (hg := hf.re.smul c.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.im),
        RealAbsolutelyIntegrable.integ_smul' (hf := hf.re)]

  rw [h_re_integ, h_im_integ, h_re_linear, h_im_linear]
  -- Need to simplify the imaginary part of (re_integ + I * im_integ)
  have h_integ_im : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).im = hf.im.integ := by
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  have h_integ_re : (↑hf.re.integ + Complex.I * ↑hf.im.integ : ℂ).re = hf.re.integ := by
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im]; ring
  -- Now just complex algebra - compare re and im parts
  apply Complex.ext
  · -- Real parts
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, sub_zero, h_integ_im, h_integ_re]
    ring
  · -- Imaginary parts
    simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
               Complex.ofReal_im, mul_zero, zero_add, h_integ_im, h_integ_re]
    ring

-- Helper: |u*f| integral equals |f| integral when |u| = 1
lemma ComplexAbsolutelyIntegrable.abs_smul_unit {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) (c: ℂ) (hc: ‖c‖ = 1) :
    (hf.smul c).abs.integ = hf.abs.integ := by
  simp only [UnsignedAbsolutelyIntegrable.integ]
  congr 1; congr 1
  funext x
  simp only [EReal.abs_fun, Pi.smul_apply, smul_eq_mul, norm_mul, hc, one_mul]

-- Helper: integ.re = re.integ for complex absolutely integrable functions
lemma ComplexAbsolutelyIntegrable.integ_re_eq_re_integ {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : hf.integ.re = hf.re.integ := by
  simp only [ComplexAbsolutelyIntegrable.integ, Complex.add_re, Complex.mul_re,
             Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

-- Main theorem: ‖∫f‖ ≤ ∫|f| for complex absolutely integrable functions
theorem ComplexAbsolutelyIntegrable.abs_le {d:ℕ} {f: EuclideanSpace' d → ℂ}
    (hf: ComplexAbsolutelyIntegrable f) : ‖hf.integ‖ ≤ hf.abs.integ := by
  by_cases h : hf.integ = 0
  · -- Case: ∫f = 0
    simp [h, UnsignedAbsolutelyIntegrable.integ]
    exact EReal.toReal_nonneg (UnsignedLebesgueIntegral.nonneg hf.abs.1)
  · -- Case: ∫f ≠ 0, use rotation trick
    -- Let u = conj(∫f) / ‖∫f‖ (a unit complex number)
    let u : ℂ := starRingEnd ℂ (hf.integ) / ‖hf.integ‖
    have hu_norm : ‖u‖ = 1 := by
      simp only [u, norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_eq_abs,
                 abs_of_nonneg (norm_nonneg _)]
      exact div_self (norm_ne_zero_iff.mpr h)
    -- Show u * ∫f = ‖∫f‖ (a real positive number)
    have h_mul : u * hf.integ = ‖hf.integ‖ := by
      simp only [u]
      rw [div_mul_eq_mul_div, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
      push_cast
      rw [sq, mul_div_assoc, div_self, mul_one]
      exact_mod_cast norm_ne_zero_iff.mpr h
    -- By linearity: ∫(u*f) = u * ∫f = ‖∫f‖
    have h_integ_smul : (hf.smul u).integ = u * hf.integ := hf.integ_smul u
    have h_integ_eq : (hf.smul u).integ = ‖hf.integ‖ := by rw [h_integ_smul, h_mul]
    -- So (∫(u*f)).re = ‖∫f‖ and equals (hf.smul u).re.integ
    have h_re : (hf.smul u).integ.re = ‖hf.integ‖ := by rw [h_integ_eq]; simp
    have h_re_integ : (hf.smul u).integ.re = (hf.smul u).re.integ := (hf.smul u).integ_re_eq_re_integ
    have h_norm_eq : (‖hf.integ‖ : ℝ) = (hf.smul u).re.integ := by rw [← h_re, h_re_integ]
    -- Chain of inequalities: ‖∫f‖ = ∫Re(u * f) ≤ ∫|Re(u * f)| ≤ ∫|u*f| = ∫|f|
    calc (‖hf.integ‖ : ℝ)
        = (hf.smul u).re.integ := h_norm_eq
      _ ≤ |(hf.smul u).re.integ| := le_abs_self _
      _ ≤ (hf.smul u).re.abs.integ := (hf.smul u).re.abs_integ_le
      _ ≤ (hf.smul u).abs.integ := (hf.smul u).re_abs_integ_le
      _ = hf.abs.integ := hf.abs_smul_unit u hu_norm

